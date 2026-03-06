//! Turtle parser (W3C RDF 1.1 Turtle specification).
//!
//! Parses the Turtle format into `Triple` values.
//! Reference: <https://www.w3.org/TR/turtle/>
//!
//! Supports: @prefix, @base, PREFIX, BASE, prefixed names, `a` shorthand,
//! predicate-object lists (`;`), object lists (`,`), blank node property
//! lists (`[ ... ]`), collections (`( ... )`), typed literals, lang-tagged
//! literals, numeric literals, boolean literals.

use crate::rdf::{BNode, Iri, Literal, RdfGraph, RdfTerm, Subject, Triple};
use std::collections::HashMap;

#[derive(Debug)]
pub struct TurtleParseError {
    pub message: String,
    pub position: usize,
}

impl std::fmt::Display for TurtleParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Turtle parse error at {}: {}", self.position, self.message)
    }
}

const RDF_TYPE: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";
const RDF_FIRST: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#first";
const RDF_REST: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest";
const RDF_NIL: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil";
const XSD_INTEGER: &str = "http://www.w3.org/2001/XMLSchema#integer";
const XSD_DECIMAL: &str = "http://www.w3.org/2001/XMLSchema#decimal";
const XSD_DOUBLE: &str = "http://www.w3.org/2001/XMLSchema#double";
const XSD_BOOLEAN: &str = "http://www.w3.org/2001/XMLSchema#boolean";

pub struct TurtleParser<'a> {
    input: &'a [u8],
    pos: usize,
    prefixes: HashMap<String, String>,
    base: Option<String>,
    graph: RdfGraph,
    bnode_labels: HashMap<String, BNode>,
}

impl<'a> TurtleParser<'a> {
    pub fn new(input: &'a str) -> Self {
        TurtleParser {
            input: input.as_bytes(),
            pos: 0,
            prefixes: HashMap::new(),
            base: None,
            graph: RdfGraph::new(),
            bnode_labels: HashMap::new(),
        }
    }

    fn err(&self, msg: &str) -> TurtleParseError {
        TurtleParseError {
            message: msg.to_string(),
            position: self.pos,
        }
    }

    fn peek(&self) -> Option<u8> {
        self.input.get(self.pos).copied()
    }

    fn advance(&mut self) -> Option<u8> {
        let b = self.input.get(self.pos).copied();
        if b.is_some() {
            self.pos += 1;
        }
        b
    }

    fn at_end(&self) -> bool {
        self.pos >= self.input.len()
    }

    fn skip_ws_and_comments(&mut self) {
        loop {
            // Skip whitespace
            while let Some(b) = self.peek() {
                if b == b' ' || b == b'\t' || b == b'\n' || b == b'\r' {
                    self.pos += 1;
                } else {
                    break;
                }
            }
            // Skip comments
            if self.peek() == Some(b'#') {
                while let Some(b) = self.peek() {
                    self.pos += 1;
                    if b == b'\n' || b == b'\r' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    fn expect(&mut self, ch: u8) -> Result<(), TurtleParseError> {
        if self.advance() == Some(ch) {
            Ok(())
        } else {
            Err(self.err(&format!("Expected '{}'", ch as char)))
        }
    }

    fn starts_with(&self, s: &[u8]) -> bool {
        self.input[self.pos..].starts_with(s)
    }

    /// Case-insensitive keyword match.
    fn match_keyword_ci(&self, keyword: &[u8], len: usize) -> bool {
        if self.pos + len > self.input.len() {
            return false;
        }
        for i in 0..len {
            if self.input[self.pos + i].to_ascii_lowercase() != keyword[i] {
                return false;
            }
        }
        true
    }

    /// Resolve a relative IRI against the base.
    fn resolve_iri(&self, iri: &str) -> String {
        if iri.contains(':') && !iri.starts_with('#') {
            // Looks absolute enough
            return iri.to_string();
        }
        if let Some(base) = &self.base {
            if iri.starts_with('#') {
                return format!("{base}{iri}");
            }
            // Strip fragment/query/path from base
            if let Some(idx) = base.rfind('/') {
                return format!("{}/{iri}", &base[..idx]);
            }
            format!("{base}{iri}")
        } else {
            iri.to_string()
        }
    }

    /// Parse an IRIREF: `<...>`
    fn parse_iriref(&mut self) -> Result<String, TurtleParseError> {
        self.expect(b'<')?;
        let mut iri = String::new();
        loop {
            match self.advance() {
                Some(b'>') => break,
                Some(b'\\') => {
                    match self.advance() {
                        Some(b'u') => {
                            let c = self.parse_hex_escape(4)?;
                            iri.push(c);
                        }
                        Some(b'U') => {
                            let c = self.parse_hex_escape(8)?;
                            iri.push(c);
                        }
                        Some(c) => return Err(self.err(&format!("Invalid IRI escape: \\{}", c as char))),
                        None => return Err(self.err("Unexpected end in IRI")),
                    }
                }
                Some(b' ') => return Err(self.err("Space in IRI")),
                Some(c) if c < 0x20 => return Err(self.err("Control character in IRI")),
                Some(c) => iri.push(c as char),
                None => return Err(self.err("Unterminated IRI")),
            }
        }
        Ok(self.resolve_iri(&iri))
    }

    fn parse_hex_escape(&mut self, n: usize) -> Result<char, TurtleParseError> {
        let mut hex = String::with_capacity(n);
        for _ in 0..n {
            match self.advance() {
                Some(c) if (c as char).is_ascii_hexdigit() => hex.push(c as char),
                _ => return Err(self.err("Invalid hex digit")),
            }
        }
        let cp = u32::from_str_radix(&hex, 16).map_err(|_| self.err("Invalid hex"))?;
        char::from_u32(cp).ok_or_else(|| self.err("Invalid Unicode code point"))
    }

    /// Peek at the current position as a full Unicode char.
    fn peek_char(&self) -> Option<char> {
        if self.pos >= self.input.len() {
            return None;
        }
        let b0 = self.input[self.pos];
        if b0 < 0x80 {
            return Some(b0 as char);
        }
        let len = if b0 < 0xE0 { 2 } else if b0 < 0xF0 { 3 } else { 4 };
        if self.pos + len > self.input.len() {
            return None;
        }
        std::str::from_utf8(&self.input[self.pos..self.pos + len])
            .ok()
            .and_then(|s| s.chars().next())
    }

    /// Parse a prefixed name like `prefix:local` or `:local`.
    fn parse_prefixed_name(&mut self) -> Result<String, TurtleParseError> {
        let mut prefix = String::new();

        // Read prefix part (before colon)
        while let Some(ch) = self.peek_char() {
            if ch == ':' {
                break;
            } else if is_pn_chars_base_unicode(ch) || ch == '_' || ch == '-' || ch == '.'
                || ch.is_ascii_digit()
            {
                prefix.push(ch);
                self.pos += ch.len_utf8();
            } else {
                break;
            }
        }

        self.expect(b':')?;

        // Read local part (after colon)
        let local = self.parse_pn_local()?;

        let ns = self.prefixes.get(&prefix).cloned().ok_or_else(|| {
            self.err(&format!("Undefined prefix: '{prefix}:'"))
        })?;

        Ok(format!("{ns}{local}"))
    }

    /// Parse a PN_LOCAL (local part of prefixed name).
    fn parse_pn_local(&mut self) -> Result<String, TurtleParseError> {
        let mut local = String::new();
        // First char: PN_CHARS_U | ':' | digit | PLX
        match self.peek_char() {
            Some('\\') => {
                self.pos += 1;
                if let Some(c) = self.advance() {
                    // Only specific chars can be escaped in PN_LOCAL
                    if is_pn_local_esc(c) {
                        local.push(c as char);
                    } else {
                        return Err(self.err(&format!("Invalid escape in prefixed name: \\{}", c as char)));
                    }
                }
            }
            Some('%') => {
                local.push_str(&self.parse_percent_encoded()?);
            }
            Some(ch) if is_pn_chars_u_unicode(ch) || ch == ':' || ch.is_ascii_digit() => {
                local.push(ch);
                self.pos += ch.len_utf8();
            }
            _ => return Ok(local), // empty local is fine
        }

        // Remaining chars
        loop {
            match self.peek_char() {
                Some('\\') => {
                    self.pos += 1;
                    if let Some(c) = self.advance() {
                        if is_pn_local_esc(c) {
                            local.push(c as char);
                        } else {
                            return Err(self.err(&format!("Invalid escape in prefixed name: \\{}", c as char)));
                        }
                    }
                }
                Some('%') => {
                    local.push_str(&self.parse_percent_encoded()?);
                }
                Some('.') => {
                    // '.' can appear in PN_LOCAL but not as last char
                    // Look ahead to next char (may be multi-byte Unicode)
                    let save = self.pos;
                    self.pos += 1; // skip the '.'
                    if let Some(next_ch) = self.peek_char() {
                        if is_pn_chars_unicode(next_ch) || next_ch == ':' || next_ch == '.' || next_ch == '%' || next_ch == '\\' {
                            local.push('.');
                            // Don't advance past next_ch - just keep going
                        } else {
                            self.pos = save; // put '.' back
                            break;
                        }
                    } else {
                        self.pos = save; // put '.' back
                        break;
                    }
                }
                Some(ch) if is_pn_chars_unicode(ch) || ch == ':' => {
                    local.push(ch);
                    self.pos += ch.len_utf8();
                }
                _ => break,
            }
        }
        Ok(local)
    }

    fn parse_percent_encoded(&mut self) -> Result<String, TurtleParseError> {
        let mut s = String::from("%");
        self.expect(b'%')?;
        for _ in 0..2 {
            match self.advance() {
                Some(c) if (c as char).is_ascii_hexdigit() => s.push(c as char),
                _ => return Err(self.err("Invalid percent encoding")),
            }
        }
        Ok(s)
    }

    /// Parse a string literal (short or long).
    fn parse_string(&mut self) -> Result<String, TurtleParseError> {
        // Check for long string (""" or ''')
        if self.starts_with(b"\"\"\"") {
            self.pos += 3;
            return self.parse_long_string(b'"');
        }
        if self.starts_with(b"'''") {
            self.pos += 3;
            return self.parse_long_string(b'\'');
        }
        // Short string
        let quote = self.advance().ok_or_else(|| self.err("Expected string"))?;
        if quote != b'"' && quote != b'\'' {
            return Err(self.err("Expected quote"));
        }
        let mut s = String::new();
        loop {
            match self.advance() {
                Some(b) if b == quote => break,
                Some(b'\\') => s.push(self.parse_string_escape()?),
                Some(b) => {
                    // Handle multi-byte UTF-8
                    if b < 0x80 {
                        s.push(b as char);
                    } else {
                        self.pos -= 1;
                        let ch = self.read_utf8_char()?;
                        s.push(ch);
                    }
                }
                None => return Err(self.err("Unterminated string")),
            }
        }
        Ok(s)
    }

    fn parse_long_string(&mut self, quote: u8) -> Result<String, TurtleParseError> {
        let mut s = String::new();
        loop {
            if self.at_end() {
                return Err(self.err("Unterminated long string"));
            }
            // Check for closing triple-quote
            if self.peek() == Some(quote) && self.pos + 2 < self.input.len()
                && self.input[self.pos + 1] == quote
                && self.input[self.pos + 2] == quote
            {
                self.pos += 3;
                break;
            }
            match self.advance() {
                Some(b'\\') => s.push(self.parse_string_escape()?),
                Some(b) => {
                    if b < 0x80 {
                        s.push(b as char);
                    } else {
                        self.pos -= 1;
                        let ch = self.read_utf8_char()?;
                        s.push(ch);
                    }
                }
                None => return Err(self.err("Unterminated long string")),
            }
        }
        Ok(s)
    }

    fn read_utf8_char(&mut self) -> Result<char, TurtleParseError> {
        let start = self.pos;
        let b0 = self.input[self.pos];
        let len = if b0 < 0x80 {
            1
        } else if b0 < 0xE0 {
            2
        } else if b0 < 0xF0 {
            3
        } else {
            4
        };
        if self.pos + len > self.input.len() {
            return Err(self.err("Invalid UTF-8"));
        }
        let s = std::str::from_utf8(&self.input[start..start + len])
            .map_err(|_| self.err("Invalid UTF-8"))?;
        self.pos += len;
        Ok(s.chars().next().unwrap())
    }

    fn parse_string_escape(&mut self) -> Result<char, TurtleParseError> {
        match self.advance() {
            Some(b't') => Ok('\t'),
            Some(b'b') => Ok('\u{0008}'),
            Some(b'n') => Ok('\n'),
            Some(b'r') => Ok('\r'),
            Some(b'f') => Ok('\u{000C}'),
            Some(b'"') => Ok('"'),
            Some(b'\'') => Ok('\''),
            Some(b'\\') => Ok('\\'),
            Some(b'u') => self.parse_hex_escape(4),
            Some(b'U') => self.parse_hex_escape(8),
            Some(c) => Err(self.err(&format!("Invalid escape: \\{}", c as char))),
            None => Err(self.err("Unexpected end")),
        }
    }

    /// Parse a blank node label `_:label`.
    fn parse_bnode_label(&mut self) -> Result<BNode, TurtleParseError> {
        self.expect(b'_')?;
        self.expect(b':')?;
        let mut label = String::new();
        // First char
        match self.peek() {
            Some(b) if is_pn_chars_u(b) || (b as char).is_ascii_digit() => {
                label.push(b as char);
                self.pos += 1;
            }
            _ => return Err(self.err("Expected blank node label")),
        }
        // Rest
        loop {
            match self.peek() {
                Some(b'.') => {
                    if self.pos + 1 < self.input.len() {
                        let next = self.input[self.pos + 1];
                        if is_pn_chars(next) || next == b'.' {
                            label.push('.');
                            self.pos += 1;
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
                Some(b) if is_pn_chars(b) => {
                    label.push(b as char);
                    self.pos += 1;
                }
                _ => break,
            }
        }
        Ok(self.bnode_labels.entry(label).or_insert_with(BNode::auto).clone())
    }

    /// Parse an IRI (IRIREF or prefixed name).
    fn parse_iri(&mut self) -> Result<String, TurtleParseError> {
        if self.peek() == Some(b'<') {
            self.parse_iriref()
        } else {
            self.parse_prefixed_name()
        }
    }

    /// Parse a subject: IRI, blank node, collection, or blank node property list.
    fn parse_subject(&mut self) -> Result<Subject, TurtleParseError> {
        self.skip_ws_and_comments();
        match self.peek() {
            Some(b'<') => {
                let iri_str = self.parse_iriref()?;
                let iri = Iri::new(&iri_str).map_err(|e| self.err(&e.to_string()))?;
                Ok(Subject::Iri(iri))
            }
            Some(b'_') => {
                let bnode = self.parse_bnode_label()?;
                Ok(Subject::BNode(bnode))
            }
            Some(b'(') => {
                let term = self.parse_collection()?;
                match term {
                    RdfTerm::Iri(i) => Ok(Subject::Iri(i)),
                    RdfTerm::BNode(b) => Ok(Subject::BNode(b)),
                    _ => Err(self.err("Collection head cannot be a literal")),
                }
            }
            Some(b'[') => {
                let bnode = self.parse_blank_node_property_list()?;
                Ok(Subject::BNode(bnode))
            }
            Some(b':') => {
                let iri_str = self.parse_prefixed_name()?;
                let iri = Iri::new(&iri_str).map_err(|e| self.err(&e.to_string()))?;
                Ok(Subject::Iri(iri))
            }
            _ => {
                // Check for Unicode PN_CHARS_BASE or ASCII alpha
                if let Some(ch) = self.peek_char() {
                    if is_pn_chars_base_unicode(ch) {
                        let iri_str = self.parse_prefixed_name()?;
                        let iri = Iri::new(&iri_str).map_err(|e| self.err(&e.to_string()))?;
                        return Ok(Subject::Iri(iri));
                    }
                }
                Err(self.err("Expected subject"))
            }
        }
    }

    /// Parse a predicate: IRI or `a`.
    fn parse_predicate(&mut self) -> Result<Iri, TurtleParseError> {
        self.skip_ws_and_comments();
        // Check for 'a' (rdf:type shorthand)
        if self.peek() == Some(b'a') {
            // Make sure it's standalone 'a', not part of a prefixed name
            let next = self.input.get(self.pos + 1).copied();
            if next.is_none() || next == Some(b' ') || next == Some(b'\t')
                || next == Some(b'\n') || next == Some(b'\r')
            {
                self.pos += 1;
                return Iri::new(RDF_TYPE).map_err(|e| self.err(&e.to_string()));
            }
        }
        let iri_str = self.parse_iri()?;
        Iri::new(&iri_str).map_err(|e| self.err(&e.to_string()))
    }

    /// Parse an object: IRI, blank node, literal, collection, or blank node property list.
    fn parse_object(&mut self) -> Result<RdfTerm, TurtleParseError> {
        self.skip_ws_and_comments();
        match self.peek() {
            Some(b'<') => {
                let iri_str = self.parse_iriref()?;
                let iri = Iri::new(&iri_str).map_err(|e| self.err(&e.to_string()))?;
                Ok(RdfTerm::Iri(iri))
            }
            Some(b'_') => {
                let bnode = self.parse_bnode_label()?;
                Ok(RdfTerm::BNode(bnode))
            }
            Some(b'"') | Some(b'\'') => self.parse_literal_value(),
            Some(b'(') => self.parse_collection(),
            Some(b'[') => {
                let bnode = self.parse_blank_node_property_list()?;
                Ok(RdfTerm::BNode(bnode))
            }
            Some(b'+') | Some(b'-') => self.parse_numeric_literal(),
            Some(b'.') => {
                // Decimal starting with '.' like .1
                self.parse_numeric_literal()
            }
            Some(b) if (b as char).is_ascii_digit() => self.parse_numeric_literal(),
            Some(b't') if self.starts_with(b"true") => {
                let next = self.input.get(self.pos + 4).copied();
                if next.is_none() || !is_pn_chars(next.unwrap()) {
                    self.pos += 4;
                    let dt = Iri::new(XSD_BOOLEAN).unwrap();
                    let lit = Literal::new("true", dt, None).map_err(|e| self.err(&e.to_string()))?;
                    return Ok(RdfTerm::Literal(lit));
                }
                // Otherwise it's a prefixed name
                let iri_str = self.parse_prefixed_name()?;
                let iri = Iri::new(&iri_str).map_err(|e| self.err(&e.to_string()))?;
                Ok(RdfTerm::Iri(iri))
            }
            Some(b'f') if self.starts_with(b"false") => {
                let next = self.input.get(self.pos + 5).copied();
                if next.is_none() || !is_pn_chars(next.unwrap()) {
                    self.pos += 5;
                    let dt = Iri::new(XSD_BOOLEAN).unwrap();
                    let lit = Literal::new("false", dt, None).map_err(|e| self.err(&e.to_string()))?;
                    return Ok(RdfTerm::Literal(lit));
                }
                let iri_str = self.parse_prefixed_name()?;
                let iri = Iri::new(&iri_str).map_err(|e| self.err(&e.to_string()))?;
                Ok(RdfTerm::Iri(iri))
            }
            Some(b':') => {
                let iri_str = self.parse_prefixed_name()?;
                let iri = Iri::new(&iri_str).map_err(|e| self.err(&e.to_string()))?;
                Ok(RdfTerm::Iri(iri))
            }
            _ => {
                // Check for Unicode PN_CHARS_BASE or ASCII alpha (prefixed name)
                if let Some(ch) = self.peek_char() {
                    if is_pn_chars_base_unicode(ch) {
                        let iri_str = self.parse_prefixed_name()?;
                        let iri = Iri::new(&iri_str).map_err(|e| self.err(&e.to_string()))?;
                        return Ok(RdfTerm::Iri(iri));
                    }
                }
                Err(self.err("Expected object"))
            }
        }
    }

    fn parse_literal_value(&mut self) -> Result<RdfTerm, TurtleParseError> {
        let lexical = self.parse_string()?;

        // Check for language tag or datatype
        if self.peek() == Some(b'@') {
            self.pos += 1;
            // Lang tag must start with a letter
            match self.peek() {
                Some(b) if (b as char).is_ascii_alphabetic() => {}
                _ => return Err(self.err("Language tag must start with a letter")),
            }
            let mut lang = String::new();
            while let Some(b) = self.peek() {
                if (b as char).is_alphanumeric() || b == b'-' {
                    lang.push(b as char);
                    self.pos += 1;
                } else {
                    break;
                }
            }
            Ok(RdfTerm::Literal(Literal::lang(&lexical, &lang)))
        } else if self.peek() == Some(b'^') && self.input.get(self.pos + 1) == Some(&b'^') {
            self.pos += 2;
            let dt_str = self.parse_iri()?;
            let dt = Iri::new(&dt_str).map_err(|e| self.err(&e.to_string()))?;
            let lit = Literal::new(&lexical, dt, None).map_err(|e| self.err(&e.to_string()))?;
            Ok(RdfTerm::Literal(lit))
        } else {
            Ok(RdfTerm::Literal(Literal::plain(&lexical)))
        }
    }

    fn parse_numeric_literal(&mut self) -> Result<RdfTerm, TurtleParseError> {
        let start = self.pos;
        // Optional sign
        if self.peek() == Some(b'+') || self.peek() == Some(b'-') {
            self.pos += 1;
        }
        let mut has_dot = false;
        let mut has_exp = false;
        let mut has_integer_part = false;
        // Integer part
        while let Some(b) = self.peek() {
            if (b as char).is_ascii_digit() {
                has_integer_part = true;
                self.pos += 1;
            } else {
                break;
            }
        }
        // Decimal part - '.' followed by digits
        if self.peek() == Some(b'.') {
            if self.pos + 1 < self.input.len() && (self.input[self.pos + 1] as char).is_ascii_digit() {
                has_dot = true;
                self.pos += 1; // consume '.'
                while let Some(b) = self.peek() {
                    if (b as char).is_ascii_digit() {
                        self.pos += 1;
                    } else {
                        break;
                    }
                }
            } else if !has_integer_part {
                // Bare dot like ".1" — consume the dot and digits after
                // Actually ".1" is valid decimal in Turtle
                has_dot = true;
                self.pos += 1;
                let mut has_frac = false;
                while let Some(b) = self.peek() {
                    if (b as char).is_ascii_digit() {
                        has_frac = true;
                        self.pos += 1;
                    } else {
                        break;
                    }
                }
                if !has_frac {
                    return Err(self.err("Invalid numeric literal"));
                }
            } else {
                // Integer followed by '.' but not digit after dot
                // Could be exponent next (e.g. "123.E+1")
                // In Turtle, this is actually a double: INTEGER '.' EXPONENT
                if self.pos + 1 < self.input.len() {
                    let after_dot = self.input[self.pos + 1];
                    if after_dot == b'e' || after_dot == b'E' {
                        has_dot = true;
                        self.pos += 1; // consume '.'
                    }
                }
            }
        }
        // Exponent
        if self.peek() == Some(b'e') || self.peek() == Some(b'E') {
            has_exp = true;
            self.pos += 1;
            if self.peek() == Some(b'+') || self.peek() == Some(b'-') {
                self.pos += 1;
            }
            let mut has_exp_digits = false;
            while let Some(b) = self.peek() {
                if (b as char).is_ascii_digit() {
                    has_exp_digits = true;
                    self.pos += 1;
                } else {
                    break;
                }
            }
            if !has_exp_digits {
                return Err(self.err("Exponent requires digits"));
            }
        }

        let text = String::from_utf8_lossy(&self.input[start..self.pos]).to_string();
        if text.is_empty() || text == "+" || text == "-" {
            return Err(self.err("Invalid numeric literal"));
        }
        let dt_str = if has_exp {
            XSD_DOUBLE
        } else if has_dot {
            XSD_DECIMAL
        } else {
            XSD_INTEGER
        };
        let dt = Iri::new(dt_str).unwrap();
        let lit = Literal::new(&text, dt, None).map_err(|e| self.err(&e.to_string()))?;
        Ok(RdfTerm::Literal(lit))
    }

    /// Parse a collection `( item1 item2 ... )` into RDF list triples.
    fn parse_collection(&mut self) -> Result<RdfTerm, TurtleParseError> {
        self.expect(b'(')?;
        self.skip_ws_and_comments();

        if self.peek() == Some(b')') {
            self.pos += 1;
            return Ok(RdfTerm::Iri(Iri::new(RDF_NIL).unwrap()));
        }

        let mut items = Vec::new();
        loop {
            self.skip_ws_and_comments();
            if self.peek() == Some(b')') {
                self.pos += 1;
                break;
            }
            items.push(self.parse_object()?);
        }

        // Build RDF list: _:b1 rdf:first item1; _:b1 rdf:rest _:b2; ...
        let first_iri = Iri::new(RDF_FIRST).unwrap();
        let rest_iri = Iri::new(RDF_REST).unwrap();
        let nil = Iri::new(RDF_NIL).unwrap();

        let nodes: Vec<BNode> = (0..items.len()).map(|_| BNode::auto()).collect();
        let head = nodes[0].clone();

        for (i, item) in items.into_iter().enumerate() {
            let s = Subject::BNode(nodes[i].clone());
            self.graph.add(Triple {
                s: s.clone(),
                p: first_iri.clone(),
                o: item,
            });
            let rest_obj = if i + 1 < nodes.len() {
                RdfTerm::BNode(nodes[i + 1].clone())
            } else {
                RdfTerm::Iri(nil.clone())
            };
            self.graph.add(Triple {
                s,
                p: rest_iri.clone(),
                o: rest_obj,
            });
        }

        Ok(RdfTerm::BNode(head))
    }

    /// Parse `[ predicate-object-list ]`.
    fn parse_blank_node_property_list(&mut self) -> Result<BNode, TurtleParseError> {
        self.expect(b'[')?;
        let bnode = BNode::auto();
        let subject = Subject::BNode(bnode.clone());

        self.skip_ws_and_comments();
        if self.peek() != Some(b']') {
            self.parse_predicate_object_list(&subject)?;
        }
        self.skip_ws_and_comments();
        self.expect(b']')?;
        Ok(bnode)
    }

    /// Parse `predicate objectList ( ';' predicate objectList )*`
    fn parse_predicate_object_list(&mut self, subject: &Subject) -> Result<(), TurtleParseError> {
        loop {
            self.skip_ws_and_comments();
            if self.peek() == Some(b']') || self.peek() == Some(b'.') || self.at_end() {
                break;
            }
            let predicate = self.parse_predicate()?;
            self.parse_object_list(subject, &predicate)?;
            self.skip_ws_and_comments();
            // Consume one or more semicolons
            if self.peek() == Some(b';') {
                while self.peek() == Some(b';') {
                    self.pos += 1;
                    self.skip_ws_and_comments();
                }
                continue;
            } else {
                break;
            }
        }
        Ok(())
    }

    /// Parse `object ( ',' object )*`
    fn parse_object_list(
        &mut self,
        subject: &Subject,
        predicate: &Iri,
    ) -> Result<(), TurtleParseError> {
        loop {
            let object = self.parse_object()?;
            self.graph.add(Triple {
                s: subject.clone(),
                p: predicate.clone(),
                o: object,
            });
            self.skip_ws_and_comments();
            if self.peek() == Some(b',') {
                self.pos += 1;
            } else {
                break;
            }
        }
        Ok(())
    }

    /// Parse a @prefix or PREFIX directive.
    fn parse_prefix_directive(&mut self) -> Result<(), TurtleParseError> {
        let is_at_prefix = self.starts_with(b"@prefix");
        if is_at_prefix {
            self.pos += 7;
        } else if self.match_keyword_ci(b"prefix", 6) {
            self.pos += 6;
        } else {
            return Err(self.err("Expected @prefix or PREFIX"));
        }
        self.skip_ws_and_comments();

        // Read prefix name (before colon)
        let mut prefix = String::new();
        while let Some(b) = self.peek() {
            if b == b':' {
                break;
            } else if b == b' ' || b == b'\t' {
                break;
            } else {
                prefix.push(b as char);
                self.pos += 1;
            }
        }
        self.expect(b':')?;
        self.skip_ws_and_comments();

        let iri = self.parse_iriref()?;
        self.skip_ws_and_comments();

        // @prefix ends with '.', SPARQL-style PREFIX does not
        if is_at_prefix {
            if self.peek() == Some(b'.') {
                self.pos += 1;
            }
        } else if self.peek() == Some(b'.') {
            // SPARQL-style PREFIX should not have '.'
            // But we'll be lenient and just skip it
            self.pos += 1;
        }

        self.prefixes.insert(prefix, iri);
        Ok(())
    }

    /// Parse a @base or BASE directive.
    fn parse_base_directive(&mut self) -> Result<(), TurtleParseError> {
        let is_at_base = self.starts_with(b"@base");
        if is_at_base {
            self.pos += 5;
        } else if self.match_keyword_ci(b"base", 4) {
            self.pos += 4;
        } else {
            return Err(self.err("Expected @base or BASE"));
        }
        self.skip_ws_and_comments();
        let iri = self.parse_iriref()?;
        self.skip_ws_and_comments();
        // @base requires '.', SPARQL-style BASE must NOT have '.'
        if is_at_base {
            if self.peek() == Some(b'.') {
                self.pos += 1;
            }
        } else {
            // SPARQL-style BASE: '.' after is a syntax error
            if self.peek() == Some(b'.') {
                return Err(self.err("SPARQL-style BASE must not be followed by '.'"));
            }
        }
        self.base = Some(iri);
        Ok(())
    }

    /// Parse the full document.
    pub fn parse(mut self) -> Result<RdfGraph, TurtleParseError> {
        loop {
            self.skip_ws_and_comments();
            if self.at_end() {
                break;
            }

            // Check for directives
            if self.starts_with(b"@prefix") {
                self.parse_prefix_directive()?;
                continue;
            }
            if self.starts_with(b"@base") {
                self.parse_base_directive()?;
                continue;
            }
            // SPARQL-style PREFIX/BASE (case-insensitive)
            if self.match_keyword_ci(b"prefix", 6) {
                self.parse_prefix_directive()?;
                continue;
            }
            if self.match_keyword_ci(b"base", 4) {
                // Make sure it's not a prefixed name starting with "base..."
                let after = self.input.get(self.pos + 4).copied();
                if after == Some(b' ') || after == Some(b'\t') || after == Some(b'\n') || after == Some(b'\r') {
                    self.parse_base_directive()?;
                    continue;
                }
            }

            // Parse a triple statement
            let subject = self.parse_subject()?;
            self.skip_ws_and_comments();

            // A subject followed by '.' is only valid for blank node property lists
            // (which already added their triples during parse_subject)
            if self.peek() == Some(b'.') {
                self.pos += 1;
                continue;
            }

            self.parse_predicate_object_list(&subject)?;
            self.skip_ws_and_comments();

            // Require '.' at end of statement
            self.skip_ws_and_comments();
            if self.peek() == Some(b'.') {
                self.pos += 1;
            } else {
                return Err(self.err("Expected '.' at end of statement"));
            }
        }

        Ok(self.graph)
    }
}

/// Parse a Turtle document into an RdfGraph.
pub fn parse(input: &str) -> Result<RdfGraph, TurtleParseError> {
    TurtleParser::new(input).parse()
}

/// Parse a Turtle document with an explicit base IRI.
pub fn parse_with_base(input: &str, base: &str) -> Result<RdfGraph, TurtleParseError> {
    let mut parser = TurtleParser::new(input);
    parser.base = Some(base.to_string());
    parser.parse()
}

// Character classification helpers (ASCII subset for byte-level checks)
fn is_pn_chars_base(b: u8) -> bool {
    b.is_ascii_alphabetic()
}

fn is_pn_chars_u(b: u8) -> bool {
    is_pn_chars_base(b) || b == b'_'
}

fn is_pn_chars(b: u8) -> bool {
    is_pn_chars_u(b) || b == b'-' || (b as char).is_ascii_digit()
}

// Unicode-aware character classification (for full Turtle compliance)
fn is_pn_chars_base_unicode(ch: char) -> bool {
    ch.is_ascii_alphabetic()
        || ('\u{00C0}'..='\u{00D6}').contains(&ch)
        || ('\u{00D8}'..='\u{00F6}').contains(&ch)
        || ('\u{00F8}'..='\u{02FF}').contains(&ch)
        || ('\u{0370}'..='\u{037D}').contains(&ch)
        || ('\u{037F}'..='\u{1FFF}').contains(&ch)
        || ('\u{200C}'..='\u{200D}').contains(&ch)
        || ('\u{2070}'..='\u{218F}').contains(&ch)
        || ('\u{2C00}'..='\u{2FEF}').contains(&ch)
        || ('\u{3001}'..='\u{D7FF}').contains(&ch)
        || ('\u{F900}'..='\u{FDCF}').contains(&ch)
        || ('\u{FDF0}'..='\u{FFFD}').contains(&ch)
        || ('\u{10000}'..='\u{EFFFF}').contains(&ch)
}

fn is_pn_chars_u_unicode(ch: char) -> bool {
    is_pn_chars_base_unicode(ch) || ch == '_'
}

fn is_pn_chars_unicode(ch: char) -> bool {
    is_pn_chars_u_unicode(ch)
        || ch == '-'
        || ch.is_ascii_digit()
        || ch == '\u{00B7}'
        || ('\u{0300}'..='\u{036F}').contains(&ch)
        || ('\u{203F}'..='\u{2040}').contains(&ch)
}

/// Characters that can be escaped in PN_LOCAL with backslash
fn is_pn_local_esc(b: u8) -> bool {
    matches!(
        b,
        b'_' | b'~' | b'.' | b'-' | b'!' | b'$' | b'&' | b'\''
            | b'(' | b')' | b'*' | b'+' | b',' | b';' | b'='
            | b'/' | b'?' | b'#' | b'@' | b'%'
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_simple_prefixed() {
        let input = r#"
@prefix : <http://example.org/> .
:s :p :o .
"#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 1);
    }

    #[test]
    fn parse_predicate_list() {
        let input = r#"
@prefix : <http://example.org/> .
:s :p1 "a" ; :p2 "b" .
"#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 2);
    }

    #[test]
    fn parse_object_list() {
        let input = r#"
@prefix : <http://example.org/> .
:s :p "a" , "b" , "c" .
"#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 3);
    }

    #[test]
    fn parse_a_shorthand() {
        let input = r#"
@prefix : <http://example.org/> .
:s a :Thing .
"#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 1);
        let t = &g.triples()[0];
        assert_eq!(t.p.as_str(), "http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
    }

    #[test]
    fn parse_typed_literal() {
        let input = r#"
@prefix : <http://example.org/> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
:s :p "42"^^xsd:integer .
"#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 1);
    }

    #[test]
    fn parse_lang_literal() {
        let input = r#"
@prefix : <http://example.org/> .
:s :p "hello"@en .
"#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 1);
    }

    #[test]
    fn parse_numeric_literals() {
        let input = r#"
@prefix : <http://example.org/> .
:s :p1 42 ; :p2 3.14 ; :p3 1.0e6 .
"#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 3);
    }

    #[test]
    fn parse_boolean_literals() {
        let input = r#"
@prefix : <http://example.org/> .
:s :p1 true ; :p2 false .
"#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 2);
    }

    #[test]
    fn parse_blank_node() {
        let input = r#"
@prefix : <http://example.org/> .
_:a :p :o .
"#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 1);
    }

    #[test]
    fn parse_blank_node_property_list() {
        let input = r#"
@prefix : <http://example.org/> .
:s :p [ :q "val" ] .
"#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 2); // :s :p _:b. AND _:b :q "val".
    }

    #[test]
    fn parse_collection_empty() {
        let input = r#"
@prefix : <http://example.org/> .
:s :p () .
"#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 1); // :s :p rdf:nil
    }

    #[test]
    fn parse_collection_items() {
        let input = r#"
@prefix : <http://example.org/> .
:s :p ("a" "b") .
"#;
        let g = parse(input).unwrap();
        // :s :p _:b1 .
        // _:b1 rdf:first "a" . _:b1 rdf:rest _:b2 .
        // _:b2 rdf:first "b" . _:b2 rdf:rest rdf:nil .
        assert_eq!(g.len(), 5);
    }

    #[test]
    fn parse_sparql_test_data() {
        // Real data from W3C SPARQL test suite
        let input = r#"
@prefix ns: <http://example.org/ns#> .
@prefix x:  <http://example.org/x/> .
@prefix z:  <http://example.org/x/#> .

x:x ns:p  "d:x ns:p" .
x:x x:p   "x:x x:p" .

z:x z:p   "z:x z:p" .
"#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 3);
    }

    #[test]
    fn parse_trailing_semicolons() {
        let input = r#"
@prefix : <http://example.org/> .
:s :p "a" ;
   :q "b" ;
.
"#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 2);
    }
}
