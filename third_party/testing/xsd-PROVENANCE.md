# W3C XML Schema Test Suite — provenance

* **Submodule path**: `third_party/testing/xsd`
* **Upstream**: <https://github.com/w3c/xsdtests>
* **Clone depth**: 1 (shallow; the suite is 214 MB of fixtures and no
  history is needed to run it).
* **Licence**: the suite's own `00COPYRIGHT` states:

  > The entire contents of this directory and all its sub-directories are
  > Copyright (C) World Wide Web Consortium 2006, 2007.
  > They are made available under the terms of the W3C DOCUMENT NOTICE AND
  > LICENSE, available online at
  > <http://www.w3.org/Consortium/Legal/copyright-documents-19990405.html>

  The W3C Document Notice and Licence permits copying and distribution of
  the documents, with the copyright notice and the licence reference
  preserved and without modification. The suite is used here UNMODIFIED,
  as a submodule pinned to an upstream commit, and is never edited in
  this repository; the runner reads it read-only.

* **Contributors named in `suite.xml`**: NIST (2004), Sun (2004, 2006),
  Microsoft (2006), Boeing (2007), Saxonica (2010), IBM (2011),
  Oracle (2011), and the W3C XML Schema Working Group.
* **Consumer**: `lake -d formal/lean4 exe l4xsd-datatypes`
  (`Harness/XsdDatatypesRun.lean`), registered in
  `tools/ensure-test-env.sh`.
* **Note on `precisionDecimal`**: the IBM and Saxonica `precisionDecimal`
  test sets are referenced from `extra-suite.xml`, not `suite.xml`, and
  are therefore outside the denominator this runner reports.
