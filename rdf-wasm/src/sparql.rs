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
    FnIsNumeric(FilterExpr),
}

#[derive(Debug, Clone)]
enum FilterExpr {
    Variable(String),
    StringLit(String),
    NumericLit(f64),
    IriLit(String),
    BooleanLit(bool),
    FnStr(Box<FilterExpr>),
    FnLang(Box<FilterExpr>),
    FnDatatype(Box<FilterExpr>),
    FnStrLen(Box<FilterExpr>),
    FnSubStr(Box<FilterExpr>, Box<FilterExpr>, Option<Box<FilterExpr>>), // str, start, len?
    FnUCase(Box<FilterExpr>),
    FnLCase(Box<FilterExpr>),
    FnConcat(Vec<FilterExpr>),
    FnAbs(Box<FilterExpr>),
    FnCeil(Box<FilterExpr>),
    FnFloor(Box<FilterExpr>),
    FnRound(Box<FilterExpr>),
    FnIf(Box<Filter>, Box<FilterExpr>, Box<FilterExpr>),
    FnCoalesce(Vec<FilterExpr>),
    FnStrBefore(Box<FilterExpr>, Box<FilterExpr>),
    FnStrAfter(Box<FilterExpr>, Box<FilterExpr>),
    FnEncodeForUri(Box<FilterExpr>),
    FnReplace(Box<FilterExpr>, String, String, Option<String>), // str, pattern, replacement, flags
    Arithmetic(Box<FilterExpr>, String, Box<FilterExpr>), // left, op (+,-,*,/), right
    // Hash functions
    FnMD5(Box<FilterExpr>),
    FnSHA1(Box<FilterExpr>),
    FnSHA256(Box<FilterExpr>),
    FnSHA384(Box<FilterExpr>),
    FnSHA512(Box<FilterExpr>),
    // Term constructors
    FnStrDt(Box<FilterExpr>, Box<FilterExpr>),   // STRDT(lexical, datatype)
    FnStrLang(Box<FilterExpr>, Box<FilterExpr>),  // STRLANG(lexical, lang)
    // Date/time accessors
    FnYear(Box<FilterExpr>),
    FnMonth(Box<FilterExpr>),
    FnDay(Box<FilterExpr>),
    FnHours(Box<FilterExpr>),
    FnMinutes(Box<FilterExpr>),
    FnSeconds(Box<FilterExpr>),
    FnTimezone(Box<FilterExpr>),
    FnTz(Box<FilterExpr>),
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
    Bind(FilterExpr, String),         // BIND(expr AS ?var)
}

#[derive(Debug, Clone)]
struct SelectExpr {
    expr: Filter, // wraps a comparison/expression that produces a value
    var: String,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum QueryForm {
    Select,
    Ask,
}

#[derive(Debug)]
struct ParsedQuery {
    form: QueryForm,
    prefixes: HashMap<String, String>,
    variables: Vec<String>, // empty = SELECT *
    select_exprs: Vec<SelectExpr>, // (expr AS ?var) in SELECT
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
    bnode_counter: usize,
    pending_clauses: Vec<WhereClause>, // generated by list pattern desugaring
}

impl Parser {
    fn new(input: &str) -> Self {
        Parser {
            tokens: tokenize(input),
            pos: 0,
            bnode_counter: 0,
            pending_clauses: Vec::new(),
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

        // Parse query form: SELECT or ASK
        let form_token = self.peek().map(|t| t.to_uppercase());
        let form = match form_token.as_deref() {
            Some("SELECT") => {
                self.next()?;
                QueryForm::Select
            }
            Some("ASK") => {
                self.next()?;
                QueryForm::Ask
            }
            _ => return Err("Expected 'SELECT' or 'ASK'".into()),
        };

        let mut variables = Vec::new();
        let mut select_exprs = Vec::new();
        let mut distinct = false;

        if form == QueryForm::Select {
            distinct = self.peek().map(|t| t.to_uppercase()) == Some("DISTINCT".to_string());
            if distinct {
                self.next()?;
            }
            // REDUCED is implementation-defined — we treat it as a no-op (keep all rows)
            if self.peek().map(|t| t.to_uppercase()) == Some("REDUCED".to_string()) {
                self.next()?;
            }

            // Variables and SELECT expressions
            if self.peek() == Some("*") {
                self.next()?;
            } else {
                while let Some(t) = self.peek() {
                    if t.starts_with('?') || t.starts_with('$') {
                        variables.push(self.next()?[1..].to_string());
                    } else if t == "(" {
                        // SELECT expression: (expr AS ?var)
                        self.next()?; // (
                        let filter = self.parse_filter()?;
                        self.expect("AS")?;
                        let var = self.next()?;
                        if !var.starts_with('?') && !var.starts_with('$') {
                            return Err(format!("Expected variable after AS, got '{var}'"));
                        }
                        self.expect(")")?;
                        let var_name = var[1..].to_string();
                        variables.push(var_name.clone());
                        select_exprs.push(SelectExpr { expr: filter, var: var_name });
                    } else {
                        break;
                    }
                }
                if variables.is_empty() {
                    return Err("Expected variable list or * after SELECT".into());
                }
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
            form,
            prefixes,
            variables,
            select_exprs,
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
            } else if upper == "BIND" {
                self.next()?; // BIND
                self.expect("(")?;
                let expr = self.parse_filter_expr()?;
                // Handle arithmetic: expr OP expr AS ?var
                let expr = if let Some(op) = self.peek() {
                    if matches!(op, "+" | "-" | "*" | "/") {
                        let arith_op = self.next()?;
                        let right = self.parse_filter_expr()?;
                        FilterExpr::Arithmetic(Box::new(expr), arith_op, Box::new(right))
                    } else {
                        expr
                    }
                } else {
                    expr
                };
                self.expect("AS")?;
                let var = self.next()?;
                if !var.starts_with('?') && !var.starts_with('$') {
                    return Err(format!("BIND expects a variable after AS, got '{var}'"));
                }
                self.expect(")")?;
                // optional trailing .
                if self.peek() == Some(".") {
                    self.next()?;
                }
                clauses.push(WhereClause::Bind(expr, var[1..].to_string()));
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
                // Drain any pending clauses from list pattern desugaring
                clauses.append(&mut self.pending_clauses);
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
        } else if t == "(" {
            // RDF list pattern — desugar to rdf:first/rdf:rest chain
            // () → rdf:nil
            // (a b c) → _:b0 rdf:first a ; rdf:rest _:b1 . _:b1 rdf:first b ; rdf:rest _:b2 . _:b2 rdf:first c ; rdf:rest rdf:nil
            let rdf_first = "http://www.w3.org/1999/02/22-rdf-syntax-ns#first".to_string();
            let rdf_rest = "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest".to_string();
            let rdf_nil = "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil".to_string();

            if self.peek() == Some(")") {
                self.next()?; // )
                Ok(PatternElement::Iri(rdf_nil))
            } else {
                // Parse list items
                let mut items = Vec::new();
                while self.peek() != Some(")") && self.peek().is_some() {
                    items.push(self.parse_pattern_element()?);
                }
                self.expect(")")?;

                // Generate blank node chain
                let mut bnodes = Vec::new();
                for _ in 0..items.len() {
                    self.bnode_counter += 1;
                    bnodes.push(format!("__list_{}", self.bnode_counter));
                }

                for (i, item) in items.iter().enumerate() {
                    let bnode_var = &bnodes[i];
                    // _:bN rdf:first item
                    self.pending_clauses.push(WhereClause::Pattern(TriplePattern {
                        s: PatternElement::Variable(bnode_var.clone()),
                        p: PatternElement::Iri(rdf_first.clone()),
                        o: item.clone(),
                    }));
                    // _:bN rdf:rest _:bN+1 (or rdf:nil for last)
                    let rest_obj = if i + 1 < items.len() {
                        PatternElement::Variable(bnodes[i + 1].clone())
                    } else {
                        PatternElement::Iri(rdf_nil.clone())
                    };
                    self.pending_clauses.push(WhereClause::Pattern(TriplePattern {
                        s: PatternElement::Variable(bnode_var.clone()),
                        p: PatternElement::Iri(rdf_rest.clone()),
                        o: rest_obj,
                    }));
                }

                // Return the first blank node as the pattern element
                Ok(PatternElement::Variable(bnodes[0].clone()))
            }
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
            "ISNUMERIC" => {
                self.next()?;
                self.expect("(")?;
                let expr = self.parse_filter_expr()?;
                self.expect(")")?;
                return Ok(Filter::FnIsNumeric(expr));
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
        let left = self.parse_filter_expr_primary()?;
        // Check for arithmetic operators after primary expression
        if let Some(op) = self.peek() {
            if matches!(op, "+" | "-" | "*" | "/") {
                let arith_op = self.next()?;
                let right = self.parse_filter_expr_primary()?;
                return Ok(FilterExpr::Arithmetic(Box::new(left), arith_op, Box::new(right)));
            }
        }
        Ok(left)
    }

    fn parse_filter_expr_primary(&mut self) -> Result<FilterExpr, String> {
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
            "STRLEN" => {
                self.next()?;
                self.expect("(")?;
                let inner = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(FilterExpr::FnStrLen(Box::new(inner)))
            }
            "SUBSTR" | "SUBSTRING" => {
                self.next()?;
                self.expect("(")?;
                let s = self.parse_filter_expr()?;
                self.expect(",")?;
                let start = self.parse_filter_expr()?;
                let len = if self.peek() == Some(",") {
                    self.next()?;
                    Some(Box::new(self.parse_filter_expr()?))
                } else {
                    None
                };
                self.expect(")")?;
                Ok(FilterExpr::FnSubStr(Box::new(s), Box::new(start), len))
            }
            "UCASE" => {
                self.next()?;
                self.expect("(")?;
                let inner = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(FilterExpr::FnUCase(Box::new(inner)))
            }
            "LCASE" => {
                self.next()?;
                self.expect("(")?;
                let inner = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(FilterExpr::FnLCase(Box::new(inner)))
            }
            "CONCAT" => {
                self.next()?;
                self.expect("(")?;
                let mut args = vec![self.parse_filter_expr()?];
                while self.peek() == Some(",") {
                    self.next()?;
                    args.push(self.parse_filter_expr()?);
                }
                self.expect(")")?;
                Ok(FilterExpr::FnConcat(args))
            }
            "ABS" => {
                self.next()?;
                self.expect("(")?;
                let inner = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(FilterExpr::FnAbs(Box::new(inner)))
            }
            "CEIL" => {
                self.next()?;
                self.expect("(")?;
                let inner = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(FilterExpr::FnCeil(Box::new(inner)))
            }
            "FLOOR" => {
                self.next()?;
                self.expect("(")?;
                let inner = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(FilterExpr::FnFloor(Box::new(inner)))
            }
            "ROUND" => {
                self.next()?;
                self.expect("(")?;
                let inner = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(FilterExpr::FnRound(Box::new(inner)))
            }
            "IF" => {
                self.next()?;
                self.expect("(")?;
                let cond = self.parse_filter()?;
                self.expect(",")?;
                let then_expr = self.parse_filter_expr()?;
                self.expect(",")?;
                let else_expr = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(FilterExpr::FnIf(Box::new(cond), Box::new(then_expr), Box::new(else_expr)))
            }
            "COALESCE" => {
                self.next()?;
                self.expect("(")?;
                let mut args = Vec::new();
                if self.peek() != Some(")") {
                    args.push(self.parse_filter_expr()?);
                    while self.peek() == Some(",") {
                        self.next()?;
                        args.push(self.parse_filter_expr()?);
                    }
                }
                self.expect(")")?;
                Ok(FilterExpr::FnCoalesce(args))
            }
            "STRBEFORE" => {
                self.next()?;
                self.expect("(")?;
                let a = self.parse_filter_expr()?;
                self.expect(",")?;
                let b = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(FilterExpr::FnStrBefore(Box::new(a), Box::new(b)))
            }
            "STRAFTER" => {
                self.next()?;
                self.expect("(")?;
                let a = self.parse_filter_expr()?;
                self.expect(",")?;
                let b = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(FilterExpr::FnStrAfter(Box::new(a), Box::new(b)))
            }
            "ENCODE_FOR_URI" => {
                self.next()?;
                self.expect("(")?;
                let inner = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(FilterExpr::FnEncodeForUri(Box::new(inner)))
            }
            "REPLACE" => {
                self.next()?;
                self.expect("(")?;
                let s = self.parse_filter_expr()?;
                self.expect(",")?;
                let pattern = self.next()?.trim_matches('"').to_string();
                self.expect(",")?;
                let replacement = self.next()?.trim_matches('"').to_string();
                let flags = if self.peek() == Some(",") {
                    self.next()?;
                    Some(self.next()?.trim_matches('"').to_string())
                } else {
                    None
                };
                self.expect(")")?;
                Ok(FilterExpr::FnReplace(Box::new(s), pattern, replacement, flags))
            }
            // Hash functions
            "MD5" | "SHA1" | "SHA256" | "SHA384" | "SHA512" => {
                let fname = upper.clone();
                self.next()?;
                self.expect("(")?;
                let inner = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(match fname.as_str() {
                    "MD5" => FilterExpr::FnMD5(Box::new(inner)),
                    "SHA1" => FilterExpr::FnSHA1(Box::new(inner)),
                    "SHA256" => FilterExpr::FnSHA256(Box::new(inner)),
                    "SHA384" => FilterExpr::FnSHA384(Box::new(inner)),
                    _ => FilterExpr::FnSHA512(Box::new(inner)),
                })
            }
            // Term constructors
            "STRDT" => {
                self.next()?;
                self.expect("(")?;
                let lexical = self.parse_filter_expr()?;
                self.expect(",")?;
                let dt = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(FilterExpr::FnStrDt(Box::new(lexical), Box::new(dt)))
            }
            "STRLANG" => {
                self.next()?;
                self.expect("(")?;
                let lexical = self.parse_filter_expr()?;
                self.expect(",")?;
                let lang = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(FilterExpr::FnStrLang(Box::new(lexical), Box::new(lang)))
            }
            // Date/time accessors
            "YEAR" | "MONTH" | "DAY" | "HOURS" | "MINUTES" | "SECONDS" | "TIMEZONE" | "TZ" => {
                let fname = upper.clone();
                self.next()?;
                self.expect("(")?;
                let inner = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(match fname.as_str() {
                    "YEAR" => FilterExpr::FnYear(Box::new(inner)),
                    "MONTH" => FilterExpr::FnMonth(Box::new(inner)),
                    "DAY" => FilterExpr::FnDay(Box::new(inner)),
                    "HOURS" => FilterExpr::FnHours(Box::new(inner)),
                    "MINUTES" => FilterExpr::FnMinutes(Box::new(inner)),
                    "SECONDS" => FilterExpr::FnSeconds(Box::new(inner)),
                    "TIMEZONE" => FilterExpr::FnTimezone(Box::new(inner)),
                    _ => FilterExpr::FnTz(Box::new(inner)),
                })
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
                    Ok(FilterExpr::BooleanLit(tok == "true"))
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
const XSD_DAYTIME_DURATION: &str = "http://www.w3.org/2001/XMLSchema#dayTimeDuration";

// --- Hash functions (pure Rust, no external crate) ---

fn md5_hash(data: &[u8]) -> u128 {
    // Simplified MD5 — uses Rust's standard approach
    // For W3C test compliance we need correct output
    use std::num::Wrapping;
    let mut a0 = Wrapping(0x67452301u32);
    let mut b0 = Wrapping(0xefcdab89u32);
    let mut c0 = Wrapping(0x98badcfeu32);
    let mut d0 = Wrapping(0x10325476u32);

    let orig_len = data.len();
    let mut msg = data.to_vec();
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    let bit_len = (orig_len as u64) * 8;
    msg.extend_from_slice(&bit_len.to_le_bytes());

    let s: [u32; 64] = [
        7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
        5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
        4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
        6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21,
    ];
    let k: [u32; 64] = [
        0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee,
        0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
        0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
        0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
        0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa,
        0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
        0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed,
        0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
        0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
        0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
        0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05,
        0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
        0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039,
        0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
        0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
        0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391,
    ];

    for chunk in msg.chunks(64) {
        let mut m = [0u32; 16];
        for (i, c) in chunk.chunks(4).enumerate() {
            m[i] = u32::from_le_bytes([c[0], c[1], c[2], c[3]]);
        }
        let (mut a, mut b, mut c, mut d) = (a0, b0, c0, d0);
        for i in 0..64 {
            let (f, g) = if i < 16 {
                ((b & c) | ((!b) & d), i)
            } else if i < 32 {
                ((d & b) | ((!d) & c), (5 * i + 1) % 16)
            } else if i < 48 {
                (b ^ c ^ d, (3 * i + 5) % 16)
            } else {
                (c ^ (b | (!d)), (7 * i) % 16)
            };
            let f = f + a + Wrapping(k[i]) + Wrapping(m[g]);
            a = d;
            d = c;
            c = b;
            b = b + Wrapping(f.0.rotate_left(s[i]));
        }
        a0 = a0 + a; b0 = b0 + b; c0 = c0 + c; d0 = d0 + d;
    }
    let bytes: [u8; 16] = [
        a0.0 as u8, (a0.0 >> 8) as u8, (a0.0 >> 16) as u8, (a0.0 >> 24) as u8,
        b0.0 as u8, (b0.0 >> 8) as u8, (b0.0 >> 16) as u8, (b0.0 >> 24) as u8,
        c0.0 as u8, (c0.0 >> 8) as u8, (c0.0 >> 16) as u8, (c0.0 >> 24) as u8,
        d0.0 as u8, (d0.0 >> 8) as u8, (d0.0 >> 16) as u8, (d0.0 >> 24) as u8,
    ];
    u128::from_be_bytes(bytes)
}

fn sha1_hash(data: &[u8]) -> String {
    use std::num::Wrapping;
    let mut h0 = Wrapping(0x67452301u32);
    let mut h1 = Wrapping(0xEFCDAB89u32);
    let mut h2 = Wrapping(0x98BADCFEu32);
    let mut h3 = Wrapping(0x10325476u32);
    let mut h4 = Wrapping(0xC3D2E1F0u32);

    let orig_len = data.len();
    let mut msg = data.to_vec();
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    let bit_len = (orig_len as u64) * 8;
    msg.extend_from_slice(&bit_len.to_be_bytes());

    for chunk in msg.chunks(64) {
        let mut w = [0u32; 80];
        for (i, c) in chunk.chunks(4).enumerate() {
            w[i] = u32::from_be_bytes([c[0], c[1], c[2], c[3]]);
        }
        for i in 16..80 {
            w[i] = (w[i-3] ^ w[i-8] ^ w[i-14] ^ w[i-16]).rotate_left(1);
        }
        let (mut a, mut b, mut c, mut d, mut e) = (h0, h1, h2, h3, h4);
        for i in 0..80 {
            let (f, k) = if i < 20 {
                ((b & c) | ((!b) & d), Wrapping(0x5A827999u32))
            } else if i < 40 {
                (b ^ c ^ d, Wrapping(0x6ED9EBA1u32))
            } else if i < 60 {
                ((b & c) | (b & d) | (c & d), Wrapping(0x8F1BBCDCu32))
            } else {
                (b ^ c ^ d, Wrapping(0xCA62C1D6u32))
            };
            let temp = Wrapping(a.0.rotate_left(5)) + f + e + k + Wrapping(w[i]);
            e = d; d = c; c = Wrapping(b.0.rotate_left(30)); b = a; a = temp;
        }
        h0 = h0 + a; h1 = h1 + b; h2 = h2 + c; h3 = h3 + d; h4 = h4 + e;
    }
    format!("{:08x}{:08x}{:08x}{:08x}{:08x}", h0.0, h1.0, h2.0, h3.0, h4.0)
}

fn sha256_hash(data: &[u8]) -> String {
    use std::num::Wrapping;
    let mut h: [Wrapping<u32>; 8] = [
        Wrapping(0x6a09e667), Wrapping(0xbb67ae85), Wrapping(0x3c6ef372), Wrapping(0xa54ff53a),
        Wrapping(0x510e527f), Wrapping(0x9b05688c), Wrapping(0x1f83d9ab), Wrapping(0x5be0cd19),
    ];
    let k: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ];
    let orig_len = data.len();
    let mut msg = data.to_vec();
    msg.push(0x80);
    while msg.len() % 64 != 56 { msg.push(0); }
    msg.extend_from_slice(&((orig_len as u64 * 8).to_be_bytes()));

    for chunk in msg.chunks(64) {
        let mut w = [0u32; 64];
        for (i, c) in chunk.chunks(4).enumerate() {
            w[i] = u32::from_be_bytes([c[0], c[1], c[2], c[3]]);
        }
        for i in 16..64 {
            let s0 = w[i-15].rotate_right(7) ^ w[i-15].rotate_right(18) ^ (w[i-15] >> 3);
            let s1 = w[i-2].rotate_right(17) ^ w[i-2].rotate_right(19) ^ (w[i-2] >> 10);
            w[i] = w[i-16].wrapping_add(s0).wrapping_add(w[i-7]).wrapping_add(s1);
        }
        let mut wh = h;
        for i in 0..64 {
            let s1 = Wrapping(wh[4].0.rotate_right(6) ^ wh[4].0.rotate_right(11) ^ wh[4].0.rotate_right(25));
            let ch = (wh[4] & wh[5]) ^ ((!wh[4]) & wh[6]);
            let temp1 = wh[7] + s1 + ch + Wrapping(k[i]) + Wrapping(w[i]);
            let s0 = Wrapping(wh[0].0.rotate_right(2) ^ wh[0].0.rotate_right(13) ^ wh[0].0.rotate_right(22));
            let maj = (wh[0] & wh[1]) ^ (wh[0] & wh[2]) ^ (wh[1] & wh[2]);
            let temp2 = s0 + maj;
            wh[7] = wh[6]; wh[6] = wh[5]; wh[5] = wh[4]; wh[4] = wh[3] + temp1;
            wh[3] = wh[2]; wh[2] = wh[1]; wh[1] = wh[0]; wh[0] = temp1 + temp2;
        }
        for i in 0..8 { h[i] = h[i] + wh[i]; }
    }
    h.iter().map(|v| format!("{:08x}", v.0)).collect()
}

// SHA-384 and SHA-512 use 64-bit words
fn sha512_core(data: &[u8], init: [u64; 8]) -> [u64; 8] {
    use std::num::Wrapping;
    let mut h: [Wrapping<u64>; 8] = init.map(Wrapping);
    let k: [u64; 80] = [
        0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
        0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
        0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
        0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
        0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
        0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
        0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
        0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
        0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
        0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
        0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
        0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
        0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
        0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
        0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
        0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
        0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
        0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
        0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
        0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
    ];
    let orig_len = data.len();
    let mut msg = data.to_vec();
    msg.push(0x80);
    while msg.len() % 128 != 112 { msg.push(0); }
    msg.extend_from_slice(&((orig_len as u128 * 8).to_be_bytes()));

    for chunk in msg.chunks(128) {
        let mut w = [0u64; 80];
        for (i, c) in chunk.chunks(8).enumerate() {
            if c.len() == 8 {
                w[i] = u64::from_be_bytes([c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]]);
            }
        }
        for i in 16..80 {
            let s0 = w[i-15].rotate_right(1) ^ w[i-15].rotate_right(8) ^ (w[i-15] >> 7);
            let s1 = w[i-2].rotate_right(19) ^ w[i-2].rotate_right(61) ^ (w[i-2] >> 6);
            w[i] = w[i-16].wrapping_add(s0).wrapping_add(w[i-7]).wrapping_add(s1);
        }
        let mut wh = h;
        for i in 0..80 {
            let s1 = Wrapping(wh[4].0.rotate_right(14) ^ wh[4].0.rotate_right(18) ^ wh[4].0.rotate_right(41));
            let ch = (wh[4] & wh[5]) ^ ((!wh[4]) & wh[6]);
            let temp1 = wh[7] + s1 + ch + Wrapping(k[i]) + Wrapping(w[i]);
            let s0 = Wrapping(wh[0].0.rotate_right(28) ^ wh[0].0.rotate_right(34) ^ wh[0].0.rotate_right(39));
            let maj = (wh[0] & wh[1]) ^ (wh[0] & wh[2]) ^ (wh[1] & wh[2]);
            let temp2 = s0 + maj;
            wh[7] = wh[6]; wh[6] = wh[5]; wh[5] = wh[4]; wh[4] = wh[3] + temp1;
            wh[3] = wh[2]; wh[2] = wh[1]; wh[1] = wh[0]; wh[0] = temp1 + temp2;
        }
        for i in 0..8 { h[i] = h[i] + wh[i]; }
    }
    h.map(|v| v.0)
}

fn sha384_hash(data: &[u8]) -> String {
    let init: [u64; 8] = [
        0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
        0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4,
    ];
    let h = sha512_core(data, init);
    // SHA-384 outputs first 6 words (384 bits)
    h[..6].iter().map(|v| format!("{:016x}", v)).collect()
}

fn sha512_hash(data: &[u8]) -> String {
    let init: [u64; 8] = [
        0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
        0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179,
    ];
    let h = sha512_core(data, init);
    h.iter().map(|v| format!("{:016x}", v)).collect()
}

// --- Date/time helpers ---

enum DtComponent { Year, Month, Day, Hours, Minutes, Seconds }

fn parse_datetime_component(dt_str: &str, component: DtComponent) -> Option<f64> {
    // Parse xsd:dateTime format: [-]YYYY-MM-DDThh:mm:ss[.sss][timezone]
    let s = dt_str.trim();
    // Split at 'T' to get date and time parts
    let (date_part, time_part) = if let Some(t_pos) = s.find('T') {
        (&s[..t_pos], Some(&s[t_pos+1..]))
    } else {
        (s, None)
    };

    match component {
        DtComponent::Year => {
            // Handle negative years
            let (neg, dp) = if date_part.starts_with('-') {
                (true, &date_part[1..])
            } else {
                (false, date_part)
            };
            let year_str = dp.split('-').next()?;
            let year: f64 = year_str.parse().ok()?;
            Some(if neg { -year } else { year })
        }
        DtComponent::Month => {
            let parts: Vec<&str> = if date_part.starts_with('-') {
                date_part[1..].split('-').collect()
            } else {
                date_part.split('-').collect()
            };
            if parts.len() >= 2 { parts[1].parse().ok() } else { None }
        }
        DtComponent::Day => {
            let parts: Vec<&str> = if date_part.starts_with('-') {
                date_part[1..].split('-').collect()
            } else {
                date_part.split('-').collect()
            };
            if parts.len() >= 3 { parts[2].parse().ok() } else { None }
        }
        DtComponent::Hours => {
            let tp = time_part?;
            let time_only = tp.split(|c| c == 'Z' || c == '+' || c == '-').next()?;
            let parts: Vec<&str> = time_only.split(':').collect();
            if !parts.is_empty() { parts[0].parse().ok() } else { None }
        }
        DtComponent::Minutes => {
            let tp = time_part?;
            let time_only = tp.split(|c| c == 'Z' || c == '+' || c == '-').next()?;
            let parts: Vec<&str> = time_only.split(':').collect();
            if parts.len() >= 2 { parts[1].parse().ok() } else { None }
        }
        DtComponent::Seconds => {
            let tp = time_part?;
            let time_only = tp.split(|c: char| c == 'Z' || (c == '+' && tp.find('T').is_none()) || (c == '-' && tp.rfind('-').map_or(false, |p| p > 0))).next()?;
            let parts: Vec<&str> = time_only.split(':').collect();
            if parts.len() >= 3 { parts[2].parse().ok() } else { None }
        }
    }
}

fn extract_timezone_duration(dt_str: &str) -> Option<String> {
    let s = dt_str.trim();
    if s.ends_with('Z') {
        Some("PT0S".to_string())
    } else if let Some(pos) = s.rfind('+').or_else(|| {
        // Find timezone '-' that's after 'T' (not the date separator)
        let t_pos = s.find('T')?;
        let after_t = &s[t_pos..];
        after_t.rfind('-').map(|p| t_pos + p)
    }) {
        let tz = &s[pos..];
        let sign = if tz.starts_with('-') { "-" } else { "" };
        let tz_parts: Vec<&str> = tz[1..].split(':').collect();
        if tz_parts.len() == 2 {
            let hours: i32 = tz_parts[0].parse().ok()?;
            let minutes: i32 = tz_parts[1].parse().ok()?;
            if hours == 0 && minutes == 0 {
                Some("PT0S".to_string())
            } else if minutes == 0 {
                Some(format!("{}PT{}H", sign, hours))
            } else {
                Some(format!("{}PT{}H{}M", sign, hours, minutes))
            }
        } else {
            None
        }
    } else {
        None // no timezone info
    }
}

fn extract_timezone_string(dt_str: &str) -> String {
    let s = dt_str.trim();
    if s.ends_with('Z') {
        "Z".to_string()
    } else if let Some(pos) = s.rfind('+').or_else(|| {
        let t_pos = s.find('T')?;
        let after_t = &s[t_pos..];
        after_t.rfind('-').map(|p| t_pos + p)
    }) {
        s[pos..].to_string()
    } else {
        String::new() // no timezone
    }
}

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
        FilterExpr::BooleanLit(b) => Some(TypedFilterValue::BooleanLiteral(*b)),
        FilterExpr::FnStrLen(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?;
            let len = v.as_string().chars().count() as f64;
            Some(TypedFilterValue::NumericLiteral(len, XSD_INTEGER.to_string()))
        }
        FilterExpr::FnSubStr(s, start, len) => {
            let sv = eval_filter_expr_typed(s, binding)?.as_string();
            let start_val = match eval_filter_expr_typed(start, binding)? {
                TypedFilterValue::NumericLiteral(n, _) => n as usize,
                _ => return None,
            };
            // SPARQL SUBSTR is 1-indexed
            let start_idx = if start_val > 0 { start_val - 1 } else { 0 };
            let chars: Vec<char> = sv.chars().collect();
            let result = if let Some(len_expr) = len {
                let len_val = match eval_filter_expr_typed(len_expr, binding)? {
                    TypedFilterValue::NumericLiteral(n, _) => n as usize,
                    _ => return None,
                };
                chars.iter().skip(start_idx).take(len_val).collect()
            } else {
                chars.iter().skip(start_idx).collect()
            };
            Some(TypedFilterValue::PlainLiteral(result))
        }
        FilterExpr::FnUCase(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?;
            match v {
                TypedFilterValue::PlainLiteral(s) => Some(TypedFilterValue::PlainLiteral(s.to_uppercase())),
                TypedFilterValue::LangLiteral(s, l) => Some(TypedFilterValue::LangLiteral(s.to_uppercase(), l)),
                _ => Some(TypedFilterValue::PlainLiteral(v.as_string().to_uppercase())),
            }
        }
        FilterExpr::FnLCase(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?;
            match v {
                TypedFilterValue::PlainLiteral(s) => Some(TypedFilterValue::PlainLiteral(s.to_lowercase())),
                TypedFilterValue::LangLiteral(s, l) => Some(TypedFilterValue::LangLiteral(s.to_lowercase(), l)),
                _ => Some(TypedFilterValue::PlainLiteral(v.as_string().to_lowercase())),
            }
        }
        FilterExpr::FnConcat(args) => {
            let mut result = String::new();
            for arg in args {
                let v = eval_filter_expr_typed(arg, binding)?;
                result.push_str(&v.as_string());
            }
            Some(TypedFilterValue::PlainLiteral(result))
        }
        FilterExpr::FnAbs(inner) => {
            match eval_filter_expr_typed(inner, binding)? {
                TypedFilterValue::NumericLiteral(n, dt) => Some(TypedFilterValue::NumericLiteral(n.abs(), dt)),
                _ => None,
            }
        }
        FilterExpr::FnCeil(inner) => {
            match eval_filter_expr_typed(inner, binding)? {
                TypedFilterValue::NumericLiteral(n, dt) => Some(TypedFilterValue::NumericLiteral(n.ceil(), dt)),
                _ => None,
            }
        }
        FilterExpr::FnFloor(inner) => {
            match eval_filter_expr_typed(inner, binding)? {
                TypedFilterValue::NumericLiteral(n, dt) => Some(TypedFilterValue::NumericLiteral(n.floor(), dt)),
                _ => None,
            }
        }
        FilterExpr::FnRound(inner) => {
            match eval_filter_expr_typed(inner, binding)? {
                TypedFilterValue::NumericLiteral(n, dt) => Some(TypedFilterValue::NumericLiteral(n.round(), dt)),
                _ => None,
            }
        }
        FilterExpr::FnIf(cond, then_expr, else_expr) => {
            if eval_filter(cond, binding) {
                eval_filter_expr_typed(then_expr, binding)
            } else {
                eval_filter_expr_typed(else_expr, binding)
            }
        }
        FilterExpr::FnCoalesce(args) => {
            for arg in args {
                if let Some(v) = eval_filter_expr_typed(arg, binding) {
                    return Some(v);
                }
            }
            None
        }
        FilterExpr::FnStrBefore(a, b) => {
            let av = eval_filter_expr_typed(a, binding)?.as_string();
            let bv = eval_filter_expr_typed(b, binding)?.as_string();
            if let Some(pos) = av.find(&bv) {
                Some(TypedFilterValue::PlainLiteral(av[..pos].to_string()))
            } else {
                Some(TypedFilterValue::PlainLiteral(String::new()))
            }
        }
        FilterExpr::FnStrAfter(a, b) => {
            let av = eval_filter_expr_typed(a, binding)?.as_string();
            let bv = eval_filter_expr_typed(b, binding)?.as_string();
            if let Some(pos) = av.find(&bv) {
                Some(TypedFilterValue::PlainLiteral(av[pos + bv.len()..].to_string()))
            } else {
                Some(TypedFilterValue::PlainLiteral(String::new()))
            }
        }
        FilterExpr::FnEncodeForUri(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?.as_string();
            let encoded: String = v.chars().map(|c| {
                if c.is_ascii_alphanumeric() || matches!(c, '-' | '_' | '.' | '~') {
                    c.to_string()
                } else {
                    let mut buf = [0u8; 4];
                    c.encode_utf8(&mut buf);
                    buf[..c.len_utf8()].iter().map(|b| format!("%{:02X}", b)).collect()
                }
            }).collect();
            Some(TypedFilterValue::PlainLiteral(encoded))
        }
        FilterExpr::FnReplace(s, pattern, replacement, flags) => {
            let sv = eval_filter_expr_typed(s, binding)?.as_string();
            let case_insensitive = flags.as_ref().map_or(false, |f| f.contains('i'));
            match RegexBuilder::new(pattern)
                .case_insensitive(case_insensitive)
                .build()
            {
                Ok(re) => {
                    let result = re.replace_all(&sv, replacement.as_str()).to_string();
                    Some(TypedFilterValue::PlainLiteral(result))
                }
                Err(_) => None,
            }
        }
        // Hash functions
        FilterExpr::FnMD5(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?.as_string();
            let digest = format!("{:x}", md5_hash(v.as_bytes()));
            Some(TypedFilterValue::PlainLiteral(digest))
        }
        FilterExpr::FnSHA1(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?.as_string();
            let digest = sha1_hash(v.as_bytes());
            Some(TypedFilterValue::PlainLiteral(digest))
        }
        FilterExpr::FnSHA256(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?.as_string();
            let digest = sha256_hash(v.as_bytes());
            Some(TypedFilterValue::PlainLiteral(digest))
        }
        FilterExpr::FnSHA384(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?.as_string();
            let digest = sha384_hash(v.as_bytes());
            Some(TypedFilterValue::PlainLiteral(digest))
        }
        FilterExpr::FnSHA512(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?.as_string();
            let digest = sha512_hash(v.as_bytes());
            Some(TypedFilterValue::PlainLiteral(digest))
        }
        // Term constructors
        FilterExpr::FnStrDt(lexical_expr, dt_expr) => {
            let lexical = eval_filter_expr_typed(lexical_expr, binding)?.as_string();
            let dt = eval_filter_expr_typed(dt_expr, binding)?.as_string();
            Some(TypedFilterValue::TypedLiteral(lexical, dt))
        }
        FilterExpr::FnStrLang(lexical_expr, lang_expr) => {
            let lexical = eval_filter_expr_typed(lexical_expr, binding)?.as_string();
            let lang = eval_filter_expr_typed(lang_expr, binding)?.as_string();
            Some(TypedFilterValue::LangLiteral(lexical, lang))
        }
        // Date/time accessors
        FilterExpr::FnYear(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?.as_string();
            let year = parse_datetime_component(&v, DtComponent::Year)?;
            Some(TypedFilterValue::NumericLiteral(year, XSD_INTEGER.to_string()))
        }
        FilterExpr::FnMonth(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?.as_string();
            let month = parse_datetime_component(&v, DtComponent::Month)?;
            Some(TypedFilterValue::NumericLiteral(month, XSD_INTEGER.to_string()))
        }
        FilterExpr::FnDay(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?.as_string();
            let day = parse_datetime_component(&v, DtComponent::Day)?;
            Some(TypedFilterValue::NumericLiteral(day, XSD_INTEGER.to_string()))
        }
        FilterExpr::FnHours(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?.as_string();
            let hours = parse_datetime_component(&v, DtComponent::Hours)?;
            Some(TypedFilterValue::NumericLiteral(hours, XSD_INTEGER.to_string()))
        }
        FilterExpr::FnMinutes(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?.as_string();
            let minutes = parse_datetime_component(&v, DtComponent::Minutes)?;
            Some(TypedFilterValue::NumericLiteral(minutes, XSD_INTEGER.to_string()))
        }
        FilterExpr::FnSeconds(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?.as_string();
            let seconds = parse_datetime_component(&v, DtComponent::Seconds)?;
            Some(TypedFilterValue::NumericLiteral(seconds, XSD_DECIMAL.to_string()))
        }
        FilterExpr::FnTimezone(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?.as_string();
            if let Some(tz) = extract_timezone_duration(&v) {
                Some(TypedFilterValue::TypedLiteral(tz, XSD_DAYTIME_DURATION.to_string()))
            } else {
                None // no timezone → error
            }
        }
        FilterExpr::FnTz(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?.as_string();
            let tz = extract_timezone_string(&v);
            Some(TypedFilterValue::PlainLiteral(tz))
        }
        FilterExpr::Arithmetic(left, op, right) => {
            let lv = eval_filter_expr_typed(left, binding)?;
            let rv = eval_filter_expr_typed(right, binding)?;
            let ln = match &lv {
                TypedFilterValue::NumericLiteral(n, _) => *n,
                _ => return None,
            };
            let rn = match &rv {
                TypedFilterValue::NumericLiteral(n, _) => *n,
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
                                } else if datatype == "http://www.w3.org/2001/XMLSchema#string"
                                    || datatype == "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"
                                {
                                    !lexical.is_empty()
                                } else {
                                    false
                                }
                            }
                            TermValue::Iri(_) | TermValue::BNode(_) => false,
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
        Filter::FnIsNumeric(expr) => {
            if let FilterExpr::Variable(name) = expr {
                matches!(binding.get(name), Some(TermValue::Literal { datatype, .. })
                    if is_numeric_type(datatype))
            } else {
                matches!(eval_filter_expr_typed(expr, binding), Some(TypedFilterValue::NumericLiteral(..)))
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
                // SPARQL algebra: OPTIONAL { P FILTER(F) } = LeftJoin(current, P, F)
                // Split inner clauses into pattern clauses and filter clauses.
                // If patterns match but filters fail, fall back to original binding.
                let patterns: Vec<WhereClause> = inner_clauses
                    .iter()
                    .filter(|c| !matches!(c, WhereClause::Filter(_)))
                    .cloned()
                    .collect();
                let filters: Vec<&Filter> = inner_clauses
                    .iter()
                    .filter_map(|c| match c {
                        WhereClause::Filter(f) => Some(f),
                        _ => None,
                    })
                    .collect();

                let mut new_results = Vec::new();
                for binding in &results {
                    let pattern_matched =
                        evaluate_clauses(&patterns, graph, vec![binding.clone()], prefixes);
                    if pattern_matched.is_empty() {
                        // No pattern match — keep original binding
                        new_results.push(binding.clone());
                    } else if filters.is_empty() {
                        // No filters — all pattern matches pass through
                        new_results.extend(pattern_matched);
                    } else {
                        // Apply filters to pattern-matched rows
                        let filtered: Vec<Binding> = pattern_matched
                            .into_iter()
                            .filter(|b| filters.iter().all(|f| eval_filter(f, b)))
                            .collect();
                        if filtered.is_empty() {
                            // All matched rows failed the filter — fall back to original binding
                            new_results.push(binding.clone());
                        } else {
                            new_results.extend(filtered);
                        }
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
            WhereClause::Bind(expr, var_name) => {
                for binding in &mut results {
                    if let Some(typed_val) = eval_filter_expr_typed(expr, binding) {
                        let term_val = match typed_val {
                            TypedFilterValue::Iri(s) => TermValue::Iri(s),
                            TypedFilterValue::BNode(s) => TermValue::BNode(s),
                            TypedFilterValue::PlainLiteral(s) => TermValue::Literal {
                                lexical: s,
                                datatype: rdf::XSD_STRING.to_string(),
                                lang: None,
                            },
                            TypedFilterValue::LangLiteral(s, l) => TermValue::Literal {
                                lexical: s,
                                datatype: "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString".to_string(),
                                lang: Some(l),
                            },
                            TypedFilterValue::NumericLiteral(n, dt) => {
                                let lexical = if dt == XSD_INTEGER {
                                    format!("{}", n as i64)
                                } else {
                                    n.to_string()
                                };
                                TermValue::Literal { lexical, datatype: dt, lang: None }
                            }
                            TypedFilterValue::TypedLiteral(s, dt) => TermValue::Literal {
                                lexical: s,
                                datatype: dt,
                                lang: None,
                            },
                            TypedFilterValue::BooleanLiteral(b) => TermValue::Literal {
                                lexical: if b { "true" } else { "false" }.to_string(),
                                datatype: XSD_BOOLEAN.to_string(),
                                lang: None,
                            },
                        };
                        if !binding.contains_key(var_name) {
                            binding.insert(var_name.clone(), term_val);
                        }
                    }
                    // If expression evaluates to None, variable stays unbound (per SPARQL spec)
                }
            }
        }
    }

    results
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Result of a SPARQL query (SELECT or ASK).
#[derive(Debug, Clone, Serialize)]
pub struct QueryResult {
    pub variables: Vec<String>,
    pub rows: Vec<Vec<Option<String>>>,
    /// For ASK queries: true if at least one solution exists, false otherwise.
    /// For SELECT queries: None.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub boolean: Option<bool>,
}

/// Execute a SPARQL query (SELECT or ASK) against the given graph.
pub fn execute(graph: &RdfGraph, query_str: &str) -> Result<QueryResult, String> {
    let mut parser = Parser::new(query_str);
    let query = parser.parse_query()?;

    let initial = vec![Binding::new()];
    let mut results = evaluate_clauses(&query.where_clauses, graph, initial, &query.prefixes);

    // ASK: return boolean result immediately — no projection, ordering, etc.
    if query.form == QueryForm::Ask {
        return Ok(QueryResult {
            variables: Vec::new(),
            rows: Vec::new(),
            boolean: Some(!results.is_empty()),
        });
    }

    // Evaluate SELECT expressions (e.g., (expr AS ?var))
    if !query.select_exprs.is_empty() {
        for binding in &mut results {
            for se in &query.select_exprs {
                let value = match &se.expr {
                    Filter::Comparison(left, op, right) => {
                        let lv = eval_filter_expr_typed(left, binding);
                        let rv = eval_filter_expr_typed(right, binding);
                        match (lv, rv) {
                            (Some(l), Some(r)) => {
                                let result = typed_compare(&l, &r, op).unwrap_or(false);
                                Some(TermValue::Literal {
                                    lexical: if result { "true" } else { "false" }.to_string(),
                                    datatype: XSD_BOOLEAN.to_string(),
                                    lang: None,
                                })
                            }
                            _ => None,
                        }
                    }
                    Filter::BooleanEffectiveValue(expr) => {
                        if let Some(typed_val) = eval_filter_expr_typed(expr, binding) {
                            let term_val = match typed_val {
                                TypedFilterValue::NumericLiteral(n, dt) => {
                                    let lexical = if dt == XSD_INTEGER {
                                        format!("{}", n as i64)
                                    } else {
                                        n.to_string()
                                    };
                                    TermValue::Literal { lexical, datatype: dt, lang: None }
                                }
                                TypedFilterValue::PlainLiteral(s) => TermValue::Literal {
                                    lexical: s,
                                    datatype: rdf::XSD_STRING.to_string(),
                                    lang: None,
                                },
                                TypedFilterValue::Iri(s) => TermValue::Iri(s),
                                TypedFilterValue::BooleanLiteral(b) => TermValue::Literal {
                                    lexical: if b { "true" } else { "false" }.to_string(),
                                    datatype: XSD_BOOLEAN.to_string(),
                                    lang: None,
                                },
                                TypedFilterValue::LangLiteral(s, l) => TermValue::Literal {
                                    lexical: s,
                                    datatype: "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString".to_string(),
                                    lang: Some(l),
                                },
                                TypedFilterValue::BNode(s) => TermValue::BNode(s),
                                TypedFilterValue::TypedLiteral(s, dt) => TermValue::Literal {
                                    lexical: s, datatype: dt, lang: None,
                                },
                            };
                            Some(term_val)
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if let Some(v) = value {
                    binding.insert(se.var.clone(), v);
                }
            }
        }
    }

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
        boolean: None,
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

    #[test]
    fn test_ask_true() {
        let g = test_graph();
        let r = execute(&g, "ASK { ?s ?p ?o }").unwrap();
        assert_eq!(r.boolean, Some(true));
        assert!(r.variables.is_empty());
        assert!(r.rows.is_empty());
    }

    #[test]
    fn test_ask_false() {
        let g = test_graph();
        let r = execute(
            &g,
            "ASK { <http://example.org/nonexistent> ?p ?o }",
        )
        .unwrap();
        assert_eq!(r.boolean, Some(false));
    }

    #[test]
    fn test_ask_with_prefix() {
        let g = test_graph();
        let r = execute(
            &g,
            r#"PREFIX foaf: <http://xmlns.com/foaf/0.1/>
               ASK { ?s foaf:name "Alice" }"#,
        )
        .unwrap();
        assert_eq!(r.boolean, Some(true));
    }

    #[test]
    fn test_ask_with_where_keyword() {
        let g = test_graph();
        let r = execute(&g, "ASK WHERE { ?s ?p ?o }").unwrap();
        assert_eq!(r.boolean, Some(true));
    }

    #[test]
    fn test_ask_empty_graph() {
        let g = RdfGraph::new();
        let r = execute(&g, "ASK { ?s ?p ?o }").unwrap();
        assert_eq!(r.boolean, Some(false));
    }
}
