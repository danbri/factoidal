fn main() {
    let data = std::fs::read_to_string("../tests/w3c/sparql/sparql10/optional/data.ttl").unwrap();
    let graph = rdf_wasm::turtle::parse(&data).unwrap();

    for (name, qfile) in [
        ("optional-001", "q-opt-1.rq"),
        ("optional-002", "q-opt-2.rq"),
        ("union-001", "q-opt-3.rq"),
    ] {
        let query = std::fs::read_to_string(format!("../tests/w3c/sparql/sparql10/optional/{}", qfile)).unwrap();
        println!("\n=== {} ===", name);
        match rdf_wasm::sparql::execute(&graph, &query) {
            Ok(r) => {
                println!("Variables: {:?}", r.variables);
                println!("Rows ({}):", r.rows.len());
                for (i, row) in r.rows.iter().enumerate() {
                    println!("  Row {}: {:?}", i, row);
                }
            }
            Err(e) => println!("ERROR: {}", e),
        }
    }

    // complex-1
    let cdata = std::fs::read_to_string("../tests/w3c/sparql/sparql10/optional/complex-data-1.ttl").unwrap();
    let cgraph = rdf_wasm::turtle::parse(&cdata).unwrap();
    let qc1 = std::fs::read_to_string("../tests/w3c/sparql/sparql10/optional/q-opt-complex-1.rq").unwrap();
    println!("\n=== complex-1 ===");
    match rdf_wasm::sparql::execute(&cgraph, &qc1) {
        Ok(r) => {
            println!("Variables: {:?}", r.variables);
            println!("Rows ({}):", r.rows.len());
            for (i, row) in r.rows.iter().enumerate() {
                println!("  Row {}: {:?}", i, row);
            }
        }
        Err(e) => println!("ERROR: {}", e),
    }

    // optional-filter tests
    let ofdata = std::fs::read_to_string("../tests/w3c/sparql/sparql10/optional-filter/data-1.ttl").unwrap();
    let ofgraph = rdf_wasm::turtle::parse(&ofdata).unwrap();
    for i in 1..=5 {
        let qf = format!("../tests/w3c/sparql/sparql10/optional-filter/expr-{}.rq", i);
        let query = std::fs::read_to_string(&qf).unwrap();
        println!("\n=== optional-filter expr-{} ===", i);
        println!("Query: {}", query.trim());
        match rdf_wasm::sparql::execute(&ofgraph, &query) {
            Ok(r) => {
                println!("Variables: {:?}", r.variables);
                println!("Rows ({}):", r.rows.len());
                for (j, row) in r.rows.iter().enumerate() {
                    println!("  Row {}: {:?}", j, row);
                }
            }
            Err(e) => println!("ERROR: {}", e),
        }
    }
}
