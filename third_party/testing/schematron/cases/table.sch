<?xml version="1.0" encoding="UTF-8"?>
<!-- Exercises the reverse document-order axis preceding-sibling, which
     Parser.XPath + XPath.Eval now support (count of preceding siblings).
     table.xml has two <row/> elements: the first has 0 preceding-sibling
     rows (0 < 1, assertion holds, no finding), the second has 1 preceding
     -sibling row (1 < 1 is false, so the assertion fails and one
     assert-fail is reported). This gives a definite pass/fail outcome
     rather than the old INDETERMINATE the deferred axis used to force.
     Source: ISO/IEC 19757-3:2016 section 5.4.3 (assert). -->
<sch:schema xmlns:sch="http://purl.oclc.org/dsdl/schematron" queryBinding="xslt">
  <sch:pattern id="row-ordering">
    <sch:rule context="row">
      <sch:assert test="count(preceding-sibling::row) &lt; 1">A row must have no preceding-sibling rows.</sch:assert>
    </sch:rule>
  </sch:pattern>
</sch:schema>
