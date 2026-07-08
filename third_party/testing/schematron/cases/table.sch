<?xml version="1.0" encoding="UTF-8"?>
<!-- Deliberately exercises the soundness discipline: preceding-sibling
     is an XPath axis that Parser.XPath defers to Stage 1.5 (see its
     module banner), so the engine cannot even parse this @test. The
     validator must record the assertion as INDETERMINATE, never a
     silent pass or fail. Source: ISO/IEC 19757-3:2016 section 5.4.3
     (assert); the axis choice targets our documented engine gap. -->
<sch:schema xmlns:sch="http://purl.oclc.org/dsdl/schematron" queryBinding="xslt">
  <sch:pattern id="row-ordering">
    <sch:rule context="row">
      <sch:assert test="count(preceding-sibling::row) &lt; 100">A table may have at most 100 preceding rows.</sch:assert>
    </sch:rule>
  </sch:pattern>
</sch:schema>
