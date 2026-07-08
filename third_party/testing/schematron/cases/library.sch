<?xml version="1.0" encoding="UTF-8"?>
<!-- Cardinality assertion. Source: ISO/IEC 19757-3:2016 section 5.4.3
     (assert), the canonical "an X must contain at least one Y" shape.
     Namespace URI per the ISO Schematron standard and the reference
     repository Schematron/schematron @ 77dcd36c53d12ed786c144ece3b2af7694abdc56. -->
<sch:schema xmlns:sch="http://purl.oclc.org/dsdl/schematron" queryBinding="xslt">
  <sch:pattern id="library-cardinality">
    <sch:rule context="library">
      <sch:assert test="count(book) >= 1">A library must contain at least one book.</sch:assert>
    </sch:rule>
  </sch:pattern>
</sch:schema>
