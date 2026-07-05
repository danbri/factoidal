open Prims
type triple =
  {
  s: RDF_Term.subject ;
  p: RDF_Term.wf_iri ;
  o: RDF_Term.rdf_term }
let __proj__Mktriple__item__s (projectee : triple) : RDF_Term.subject=
  match projectee with | { s; p; o;_} -> s
let __proj__Mktriple__item__p (projectee : triple) : RDF_Term.wf_iri=
  match projectee with | { s; p; o;_} -> p
let __proj__Mktriple__item__o (projectee : triple) : RDF_Term.rdf_term=
  match projectee with | { s; p; o;_} -> o
let triple_eq (a : triple) (b : triple) : Prims.bool=
  ((RDF_Term.subject_eq a.s b.s) && (a.p = b.p)) &&
    (RDF_Term.rdf_term_eq a.o b.o)
