//! RDF Core 1.1 graph library — executable types derived from the F* specification.
//!
//! Targets WebAssembly with JavaScript bindings via wasm-bindgen.

mod rdf;
pub mod ntriples;
pub mod sparql;
pub mod turtle;
mod wasm_api;

pub use rdf::*;
