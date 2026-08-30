# Segmented IBK design decision

Date: 2026-08-30

## Problem

`IBK1` stores all ID rows in one source-order sequence.  Its decoded
`IndexedBlock` has an in-memory predicate partition, but opening the file must
currently decode every row before that partition exists.  This defeats
predicate-bound selective I/O.

## V2 physical rule

`IBK2` will retain the existing shared term dictionary, then contain a checked
directory of predicate segments.  Each segment is contiguous and contains:

```text
predicate TermId
row count
(originalRowPosition, subjectId, predicateId, objectId)*
```

The directory records each segment's byte offset and length.  A predicate-bound
scan can read only its segment.  `originalRowPosition` preserves the current
observable source ordering: rows from a selected segment are reordered by this
position before they reach the existing SPARQL backend.  An unbound scan uses
the same positions to reconstruct all source order.

## Safety gates

- offsets and lengths must lie within the CRC-covered payload;
- segment predicate IDs and each row's predicate ID must agree;
- every original row position is unique and in range;
- decoded terms and row IDs retain V1's validation;
- the first theorem target is denotation equality with the input ordered block,
  followed by equality of predicate-bound `scanBound` results.

This deliberately separates an ordered physical-block codec from later
content-addressed RDF graph normalization.
