# Vendored W3C RIF Test Cases (curated subset)

The four SPARQL 1.1 entailment tests rif01/rif03/rif04/rif06 reference
companion RIF-XML rule documents that are not bundled with the SPARQL
test suite at `third_party/testing/w3c/sparql/sparql11/entailment/`.
This directory holds a curated subset, mirrored from the W3C RIF Test
Cases repository at:

    https://www.w3.org/2005/rules/test/repository/tc/

Date of mirror: 2026-05-07. Source listing was the directory index of
the repository above.

## Files

| SPARQL test | RIF source | Local path                                                               |
|-------------|-----------|--------------------------------------------------------------------------|
| rif01       | (synthesised — see note)               | `tc/Logical_entailment_referencing_RIF_XML/rif01-premise.rif` |
| rif03       | tc/Frames                              | `tc/Frames/Frames-premise.rif`, `Frames-conclusion.rif`        |
| rif04       | tc/Modeling_Brain_Anatomy              | `tc/Modeling_Brain_Anatomy/Modeling_Brain_Anatomy-premise.rif`, plus `import001.rdf`, `conclusion.rif` |
| rif06       | tc/RDF_Combination_Blank_Node          | `tc/RDF_Combination_Blank_Node/RDF_Combination_Blank_Node-premise.rif`, plus `import001.rdf`, `conclusion.rif` |

## rif01 — synthesised premise

The W3C RIF tc/ repository does not contain a test case named
"Logical entailment referencing RIF XML". The SPARQL Working Group's
entailment manifest references `<rif01.rif>` as a peer file but the
file was never published. We reconstruct the rule from the .ttl
premise (parent + brother facts) and the .srx expected result
(ex:Emeka ex:uncle ex:Chijoke), encoded as RIF Core XML in the same
style as the four sibling premise files.

## License

The contents of the `tc/` mirror are W3C documents distributed under
the W3C Document License,
https://www.w3.org/Consortium/Legal/2002/copyright-documents-20021231.
The synthesised rif01 premise is provided under the same license for
consistency. See the W3C copyright page for the terms.

## Why a vendor copy and not a submodule?

The W3C RIF tests are not maintained in a public git repository at
the time of mirroring. The only canonical distribution is the static
HTTP directory listed above. A curated copy of the four test cases
(rif01/rif03/rif04/rif06) is the minimum needed to drive
`formal/fstar/RIF.Core.Tests.fst` against the SPARQL 1.1 entailment
manifest in `third_party/testing/w3c/sparql/sparql11/entailment/`.
