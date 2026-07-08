<?xml version="1.0" encoding="UTF-8"?>
<!-- Co-occurrence / cardinality constraint. Source: the canonical
     "a car has four wheels" example from Rick Jelliffe's Schematron
     tutorial (schematron.com, "The Schematron Assertion Language")
     and ISO/IEC 19757-3:2016 section 5.4.3. -->
<sch:schema xmlns:sch="http://purl.oclc.org/dsdl/schematron" queryBinding="xslt">
  <sch:pattern id="car-wheels">
    <sch:rule context="car">
      <sch:assert test="count(wheel) = 4">A car must have exactly four wheels.</sch:assert>
    </sch:rule>
  </sch:pattern>
</sch:schema>
