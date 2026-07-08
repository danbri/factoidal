<?xml version="1.0" encoding="UTF-8"?>
<!-- Forbidden-combination report. Source: ISO/IEC 19757-3:2016
     section 5.4.4 (report fires when its test is TRUE) applied to a
     mutually-exclusive-attribute co-occurrence constraint. -->
<sch:schema xmlns:sch="http://purl.oclc.org/dsdl/schematron" queryBinding="xslt">
  <sch:pattern id="book-flag-exclusivity">
    <sch:rule context="book">
      <sch:report test="@discount and @clearance">A book must not be both discounted and on clearance.</sch:report>
    </sch:rule>
  </sch:pattern>
</sch:schema>
