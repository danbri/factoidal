//! N-Triples parser (W3C RDF 1.1 N-Triples specification).
//!
//! Parses the N-Triples format into `Triple` values.
//! Reference: <https://www.w3.org/TR/n-triples/>

use std::collections::HashMap;
use crate::rdf::{BNode, Iri, Literal, RdfGraph, RdfTerm, Subject, Triple};

#[derive(Debug)]
pub struct ParseError {
    pub line: usize,
    pub message: String,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Line {}: {}", self.line, self.message)
    }
}

/// Parse an N-Triples document into an RdfGraph.
pub fn parse(input: &str) -> Result<RdfGraph, ParseError> {
    let mut graph = RdfGraph::new();
    let mut bnode_labels: HashMap<String, BNode> = HashMap::new();
    for (line_num, line) in input.lines().enumerate() {
        let line = line.trim();
        // Skip empty lines and comments
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let triple = parse_triple(line, line_num + 1, &mut bnode_labels)?;
        graph.add(triple);
    }
    Ok(graph)
}

/// Parse a single N-Triples line into a Triple.
fn parse_triple(line: &str, line_num: usize, bnode_labels: &mut HashMap<String, BNode>) -> Result<Triple, ParseError> {
    let mut chars = line.chars().peekable();
    let err = |msg: &str| ParseError {
        line: line_num,
        message: msg.to_string(),
    };

    skip_whitespace(&mut chars);

    let mut dot_consumed = false;

    // Parse subject (IRI or bnode)
    let s = if chars.peek() == Some(&'<') {
        let iri = parse_iri_ref(&mut chars).map_err(|m| err(&m))?;
        Subject::Iri(Iri::new(&iri).map_err(|e| err(&e.to_string()))?)
    } else if chars.peek() == Some(&'_') {
        let (id, dc) = parse_bnode_label(&mut chars).map_err(|m| err(&m))?;
        dot_consumed = dc;
        Subject::BNode(bnode_labels.entry(id).or_insert_with(BNode::auto).clone())
    } else {
        return Err(err("Expected '<' or '_:' for subject"));
    };

    if !dot_consumed {
        skip_whitespace(&mut chars);
    }

    // Parse predicate (IRI only)
    let p = if chars.peek() == Some(&'<') {
        let iri = parse_iri_ref(&mut chars).map_err(|m| err(&m))?;
        Iri::new(&iri).map_err(|e| err(&e.to_string()))?
    } else {
        return Err(err("Expected '<' for predicate"));
    };

    skip_whitespace(&mut chars);

    // Parse object (IRI, bnode, or literal)
    let o = if chars.peek() == Some(&'<') {
        let iri = parse_iri_ref(&mut chars).map_err(|m| err(&m))?;
        RdfTerm::Iri(Iri::new(&iri).map_err(|e| err(&e.to_string()))?)
    } else if chars.peek() == Some(&'_') {
        let (id, dc) = parse_bnode_label(&mut chars).map_err(|m| err(&m))?;
        dot_consumed = dc;
        RdfTerm::BNode(bnode_labels.entry(id).or_insert_with(BNode::auto).clone())
    } else if chars.peek() == Some(&'"') {
        parse_literal(&mut chars).map_err(|m| err(&m))?
    } else {
        return Err(err("Expected '<', '_:', or '\"' for object"));
    };

    if !dot_consumed {
        skip_whitespace(&mut chars);
    }

    // Expect '.' (may have been consumed by bnode parser)
    if dot_consumed {
        // Already consumed
    } else if chars.next() != Some('.') {
        return Err(err("Expected '.' at end of triple"));
    }

    Ok(Triple { s, p, o })
}

fn skip_whitespace(chars: &mut std::iter::Peekable<std::str::Chars>) {
    while let Some(&c) = chars.peek() {
        if c == ' ' || c == '\t' {
            chars.next();
        } else {
            break;
        }
    }
}

/// Parse `<IRI>` and return the IRI string (without angle brackets).
fn parse_iri_ref(
    chars: &mut std::iter::Peekable<std::str::Chars>,
) -> Result<String, String> {
    if chars.next() != Some('<') {
        return Err("Expected '<'".into());
    }
    let mut iri = String::new();
    loop {
        match chars.next() {
            Some('>') => break,
            Some('\\') => {
                // Handle \uXXXX and \UXXXXXXXX escapes
                match chars.next() {
                    Some('u') => {
                        let cp = parse_hex_escape(chars, 4)?;
                        iri.push(cp);
                    }
                    Some('U') => {
                        let cp = parse_hex_escape(chars, 8)?;
                        iri.push(cp);
                    }
                    Some(c) => {
                        return Err(format!("Invalid escape in IRI: \\{c}"));
                    }
                    None => return Err("Unexpected end of IRI".into()),
                }
            }
            Some(c) if c == ' ' || (c as u32) < 0x20 => {
                return Err(format!("Invalid character in IRI: U+{:04X}", c as u32));
            }
            Some(c) => iri.push(c),
            None => return Err("Unterminated IRI".into()),
        }
    }
    Ok(iri)
}

/// Parse `_:label` and return the label string and whether a trailing '.'
/// was consumed (which is the statement terminator, not part of the label).
fn parse_bnode_label(
    chars: &mut std::iter::Peekable<std::str::Chars>,
) -> Result<(String, bool), String> {
    if chars.next() != Some('_') {
        return Err("Expected '_'".into());
    }
    if chars.next() != Some(':') {
        return Err("Expected '_:'".into());
    }
    let mut label = String::new();
    let mut consumed_trailing_dot = false;
    while let Some(&c) = chars.peek() {
        if c == '.' {
            // Consume the '.' tentatively
            chars.next();
            if let Some(&next) = chars.peek() {
                if next.is_alphanumeric() || next == '_' || next == '-' || next == '.' {
                    // '.' is internal to the label
                    label.push('.');
                    continue;
                }
            }
            // '.' is the trailing dot (statement terminator or end-of-label)
            consumed_trailing_dot = true;
            break;
        } else if c.is_alphanumeric() || c == '_' || c == '-' {
            label.push(c);
            chars.next();
        } else {
            break;
        }
    }
    if label.is_empty() {
        return Err("Empty blank node label".into());
    }
    Ok((label, consumed_trailing_dot))
}

/// Parse a literal: `"string"`, optionally followed by `@lang` or `^^<datatype>`.
fn parse_literal(
    chars: &mut std::iter::Peekable<std::str::Chars>,
) -> Result<RdfTerm, String> {
    if chars.next() != Some('"') {
        return Err("Expected '\"'".into());
    }
    let mut lexical = String::new();
    loop {
        match chars.next() {
            Some('"') => break,
            Some('\\') => {
                match chars.next() {
                    Some('t') => lexical.push('\t'),
                    Some('b') => lexical.push('\u{0008}'),
                    Some('n') => lexical.push('\n'),
                    Some('r') => lexical.push('\r'),
                    Some('f') => lexical.push('\u{000C}'),
                    Some('"') => lexical.push('"'),
                    Some('\'') => lexical.push('\''),
                    Some('\\') => lexical.push('\\'),
                    Some('u') => {
                        let cp = parse_hex_escape(chars, 4)?;
                        lexical.push(cp);
                    }
                    Some('U') => {
                        let cp = parse_hex_escape(chars, 8)?;
                        lexical.push(cp);
                    }
                    Some(c) => return Err(format!("Invalid escape: \\{c}")),
                    None => return Err("Unexpected end of literal".into()),
                }
            }
            Some(c) => lexical.push(c),
            None => return Err("Unterminated literal".into()),
        }
    }

    // Check for language tag or datatype
    if chars.peek() == Some(&'@') {
        chars.next(); // consume @
        let mut lang = String::new();
        // BCP 47: language tag must start with a letter
        match chars.peek() {
            Some(&c) if c.is_ascii_alphabetic() => {}
            _ => return Err("Language tag must start with a letter".into()),
        }
        while let Some(&c) = chars.peek() {
            if c.is_alphanumeric() || c == '-' {
                lang.push(c);
                chars.next();
            } else {
                break;
            }
        }
        if lang.is_empty() {
            return Err("Empty language tag".into());
        }
        Ok(RdfTerm::Literal(Literal::lang(&lexical, &lang)))
    } else if chars.peek() == Some(&'^') {
        chars.next(); // first ^
        if chars.next() != Some('^') {
            return Err("Expected '^^'".into());
        }
        let dt_str = parse_iri_ref(chars)?;
        let dt = Iri::new(&dt_str).map_err(|e| e.to_string())?;
        let lit = Literal::new(&lexical, dt, None).map_err(|e| e.to_string())?;
        Ok(RdfTerm::Literal(lit))
    } else {
        // Plain literal (xsd:string)
        Ok(RdfTerm::Literal(Literal::plain(&lexical)))
    }
}

/// Parse N hex digits into a Unicode code point.
fn parse_hex_escape(
    chars: &mut std::iter::Peekable<std::str::Chars>,
    n: usize,
) -> Result<char, String> {
    let mut hex = String::with_capacity(n);
    for _ in 0..n {
        match chars.next() {
            Some(c) if c.is_ascii_hexdigit() => hex.push(c),
            Some(c) => return Err(format!("Invalid hex digit: {c}")),
            None => return Err("Unexpected end of hex escape".into()),
        }
    }
    let cp = u32::from_str_radix(&hex, 16)
        .map_err(|_| format!("Invalid hex: {hex}"))?;
    char::from_u32(cp).ok_or_else(|| format!("Invalid Unicode code point: U+{hex}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_simple_triple() {
        let input = r#"<http://example/s> <http://example/p> <http://example/o> ."#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 1);
    }

    #[test]
    fn parse_string_literal() {
        let input = r#"<http://example/s> <http://example/p> "string" ."#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 1);
        let nt = g.to_ntriples();
        assert!(nt.contains("\"string\""));
    }

    #[test]
    fn parse_lang_literal() {
        let input = r#"<http://example/s> <http://example/p> "hello"@en ."#;
        let g = parse(input).unwrap();
        let nt = g.to_ntriples();
        assert!(nt.contains("\"hello\"@en"));
    }

    #[test]
    fn parse_typed_literal() {
        let input = r#"<http://example/s> <http://example/p> "42"^^<http://www.w3.org/2001/XMLSchema#integer> ."#;
        let g = parse(input).unwrap();
        let nt = g.to_ntriples();
        assert!(nt.contains("^^<http://www.w3.org/2001/XMLSchema#integer>"));
    }

    #[test]
    fn parse_bnode() {
        let input = r#"_:a <http://example/p> <http://example/o> ."#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 1);
        assert!(!g.bnodes().is_empty());
    }

    #[test]
    fn parse_escape_sequences() {
        let input = r#"<http://example/s> <http://example/p> "tab\there" ."#;
        let g = parse(input).unwrap();
        let nt = g.to_ntriples();
        assert!(nt.contains("\\t"));
    }

    #[test]
    fn parse_unicode_escape() {
        let input = r#"<http://example/s> <http://example/p> "\u00E9" ."#;
        let g = parse(input).unwrap();
        let nt = g.to_ntriples();
        assert!(nt.contains('é'));
    }

    #[test]
    fn skip_comments_and_empty() {
        let input = "# comment\n\n<http://example/s> <http://example/p> <http://example/o> .\n# another comment\n";
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 1);
    }

    #[test]
    fn multiple_triples() {
        let input = r#"<http://example/s> <http://example/p1> "a" .
<http://example/s> <http://example/p2> "b" .
<http://example/s> <http://example/p3> <http://example/o> ."#;
        let g = parse(input).unwrap();
        assert_eq!(g.len(), 3);
    }

    #[test]
    fn reject_bad_syntax() {
        // Missing period
        assert!(parse(r#"<http://example/s> <http://example/p> "x""#).is_err());
        // Empty input is OK (zero triples)
        assert!(parse("").is_ok());
        assert!(parse("# just a comment").is_ok());
    }
}
