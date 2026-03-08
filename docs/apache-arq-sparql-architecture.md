# How Apache ARQ Represents SPARQL Syntax and Its Derivation from the W3C Specification

Apache ARQ (the query engine inside Apache Jena) follows a **multi-stage representation pipeline** that mirrors the structure of the SPARQL specification. Understanding this pipeline is useful when designing a verified implementation.

---

# 1. Text -> Query object (syntax layer)

ARQ first parses SPARQL text using a parser built with JavaCC. The root API is the class `SPARQLParser`.

Example entry point:

```java
Query q = QueryFactory.create("SELECT * WHERE { ?s ?p ?o }");
```

This produces a **Query object**, which is essentially a structured representation of the query syntax.

Typical fields in the `Query` object include:

- query type (SELECT / ASK / CONSTRUCT / DESCRIBE)
- projection variables
- dataset clauses (`FROM`, `FROM NAMED`)
- modifiers (`DISTINCT`, `ORDER BY`, etc.)
- the **query pattern**

The query pattern is the main body of `WHERE`.

Internally this becomes a tree of **syntax elements** such as:

```
ElementGroup
ElementTriplesBlock
ElementFilter
ElementOptional
ElementUnion
ElementSubQuery
ElementBind
ElementService
ElementNamedGraph
```

These live under packages like:

```
org.apache.jena.sparql.syntax
```

Conceptually this stage corresponds to **the SPARQL grammar in the W3C specification**.
It is still very close to the original textual form.

---

# 2. Query AST -> SPARQL algebra

Next ARQ runs the **translation defined in the W3C SPARQL specification**.

In code:

```java
Op op = Algebra.compile(query);
```

This converts the syntax tree into **SPARQL algebra operators**.

Example:

```
SELECT * WHERE { ?s ?p ?o }
```

becomes algebra roughly like:

```
(project (?s ?p ?o)
   (bgp
      (triple ?s ?p ?o)))
```

The algebra objects are classes implementing interface `Op`.

Examples:

```
OpBGP
OpJoin
OpLeftJoin
OpUnion
OpFilter
OpProject
OpGraph
OpExtend
OpSlice
OpOrder
OpDistinct
```

All live under:

```
org.apache.jena.sparql.algebra.op
```

This stage corresponds to **section 12 of the SPARQL specification (SPARQL Algebra)**.

---

# 3. Algebra -> optimized algebra

ARQ then runs algebra **rewrite passes**.

Examples include:

- filter placement
- equality simplification
- implicit join detection
- property function expansion

These are implemented as transformations over algebra trees:

```
TransformFilterPlacement
TransformFilterEquality
TransformImplicitLeftJoin
```

These transformations rewrite the algebra into equivalent forms.

This corresponds to **query optimization rules**.

---

# 4. Algebra -> execution plan

Next the algebra becomes a **query plan** consisting of iterators.

Examples:

```
QueryIterJoin
QueryIterFilter
QueryIterProject
QueryIterDistinct
```

The execution model is **iterator-based (pipeline)**:

```
Binding iterator
-> next binding
-> propagate to next operator
```

Bindings represent **solution mappings**.

---

# 5. Execution

Finally the iterators evaluate against a dataset.

Low-level storage engines (TDB, in-memory graph etc.) influence:

- index selection
- triple ordering
- join strategies

But the algebra remains the high-level semantic contract.

---

# 6. ARQ's intermediate representation: SSE

ARQ also exposes the algebra using **SPARQL S-Expressions (SSE)**.

Example:

```
(project (?s ?p ?o)
  (bgp
    (triple ?s ?p ?o)))
```

This format is both:

- printable
- parseable back into algebra

ARQ CLI example:

```
arq.qparse --print=op query.rq
```

---

# 7. Mapping to the SPARQL spec

The architecture mirrors the specification deliberately.

| W3C spec section | ARQ representation |
|------------------|-------------------|
| SPARQL grammar | parser -> Query AST |
| Graph pattern semantics | syntax tree elements |
| Algebra translation rules | `Algebra.compile` |
| Algebra operators | `Op*` classes |
| Evaluation semantics | iterator engine |

ARQ effectively encodes **the specification's algebra model almost verbatim**.

---

# 8. Important design implication

ARQ separates three semantic layers:

```
text syntax
      |
syntax AST
      |
SPARQL algebra
      |
execution operators
```

The **algebra layer is the semantic pivot**.

Everything above it is syntax.
Everything below it is execution strategy.

That separation is ideal if your goal is **formal verification**.

---

# 9. Key lessons for a verified SPARQL implementation

A good architecture usually mirrors ARQ's separation.

You want:

### Layer 1 -- syntax

```
query text -> AST
```

Pure parsing.

### Layer 2 -- algebra

```
AST -> algebra
```

This is the **spec semantics layer**.

If you formalize anything in F*, it should likely be **this layer**.

### Layer 3 -- logical evaluation

```
algebra -> solution mappings
```

Define evaluation rules.

### Layer 4 -- execution strategy

```
join ordering
indexes
streaming
caching
```

All optimizations must refine layer 3.

---

# 10. Where ARQ is slightly messy

ARQ is a production system, not a formalization.

So there are compromises:

- algebra sometimes extended beyond spec
- execution iterators sometimes mix optimization and semantics
- dataset semantics partially embedded in execution layer
- bag semantics implicit in iterator behavior

These are areas where a **formal implementation could be cleaner**.

---

# 11. Why ARQ is still a good reference

ARQ has two valuable properties:

1. **Very close to the W3C algebra model**
2. **Battle-tested against the full W3C test suite**

That makes it a useful empirical reference when designing a verified engine.
